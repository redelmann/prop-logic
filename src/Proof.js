import { constant, meta, implies, and, or, iff, not, xor, exprToString } from "./Expr.js";
import { getConstraints, solveConstraints, substituteMetaVariables, unify } from "./Unify.js";
import { parse } from "./Parser.js";

export class Part {
    constructor(root, parent, position) {
        this.root = root;
        this.parent = parent;
        this.number = -1;
        this.position = position;
        this.listeners = [];
        this.all_dependents = {};
        this.actual_dependents = {};
        this.id = root.nextId();
        this.fixed = false;
        this.deleted = false;
    }

    _delete() {
        this.deleted = true;
        Object.values(this.actual_dependents).forEach(dependent =>
            dependent.removeDependency(this));
        this.parent.unlinkPart(this);
    }

    transitiveDependents() {
        const trans_dependents = new Set();
        const working_list = [];

        add_dependent(this);
        
        function add_dependent(dependent) {
            if (!trans_dependents.has(dependent)) {
                dependent.setDirty();
                trans_dependents.add(dependent);
                working_list.push(dependent);
            }
        }

        while (working_list.length > 0) {
            const part = working_list.pop();

            part.dependents.forEach(add_dependent);
            if (part.parent) {
                add_dependent(part.parent);
            }
        }

        return trans_dependents;
    }

    notifyAll(event) {
        const trans_dependents = this.transitiveDependents();

        // Notify all dependents that transitively_ok has changed
        trans_dependents.forEach(dependent => {
            dependent.notify(event);
        });
    }

    renumber(n, p) {
        this.number = n;
        this.position = p;
    }

    addListener(listener) {
        this.listeners.push(listener);
    }

    removeListener(listener) {
        const index = this.listeners.indexOf(listener);
        if (index !== -1) {
            this.listeners.splice(index, 1);
        }
    }

    notify(event) {
        for (let i = 0; i < this.listeners.length; i++) {
            this.listeners[i](event);
        }
    }

    get dependents() {
        return Object.values(this.actual_dependents);
    }

    addDependent(dependent) {
        if (!(dependent.id in this.all_dependents)) {
            this.actual_dependents[dependent.id] = dependent;
            this.all_dependents[dependent.id] = 0;
        }
        this.all_dependents[dependent.id]++;
    }

    removeDependent(dependent) {
        this.all_dependents[dependent]--;
        if (this.all_dependents[dependent] === 0) {
            delete this.all_dependents[dependent];
            delete this.actual_dependents[dependent];
        }
    }

    get context() {
        if (this.parent === this.root) {
            return [];
        }
        else {
            return this.parent.context.concat([this.parent.position]);
        }
    }

    get last_number() {
        return this.number + this.size - 1;
    }
}


export class Line extends Part {
    constructor(root, parent, position) {
        super(root, parent, position);

        this.expr = null;
        this.malformed_expr = false;
        this.rule = null;
        this.refs = [];
        this.refs_listeners = [];
        this.size = 1;
        this.listeners = [];
        this.status_cache = null;
    }

    toJSON() {
        return {
            type: "line",
            expr: this.expr !== null ? exprToString(this.expr) : null,
            rule: this.rule !== null ? this.rule.name : null,
            refs: this.refs.map(ref => ref !== null ? ref.range : null),
        };
    }

    setDirty() {
        this.status_cache = null;
        this.parent.setDirty();
    }

    display(indent) {
        let s = "";
        for (let i = 0; i < indent; i++) {
            s += "  ";
        }
        s = this.number + ": " + s;
        if (this.expr !== null) {
            s += exprToString(this.expr);
        }
        else {
            s += "???";
        }
        s += " by "
        if (this.rule !== null) {
            s += this.rule.name;
        }
        else {
            s += "???";
        }
        if (this.refs.length > 0) {
            s += " from ";
            for (let i = 0; i < this.refs.length; i++) {
                if (i > 0) {
                    s += ", ";
                }
                if (this.refs[i] !== null) {
                    s += this.refs[i].range;
                }
                else {
                    s += "???";
                }
            }
        }
        s += " " + (this.status.ok ? "OK" : "ERROR");
        s += " " + this.position;
        console.log(s);
    }

    setMalformedExpr() {
        this.setDirty();
        this.expr = null;
        this.malformed_expr = true;
        this.notify({ message: "expr_changed" });
        this.notifyAll({ message: "dirty" });
    }

    setExpr(expr) {
        this.setDirty();
        this.expr = expr;
        this.malformed_expr = false;
        this.notify({ message: "expr_changed" });
        this.notifyAll({ message: "dirty" });
    }

    setRule(rule) {
        this.setDirty();
        this.rule = rule;

        if (rule === null) {
            this.refs = [];
        }
        else {
            const size = rule.parts.length + rule.subproofs.length;
            this.refs = new Array(size).fill(null);
        }
        this.notify({ message: "rule_changed" });
        this.notifyAll({ message: "dirty" });
    }

    setRef(index, ref) {
        this.setDirty();
        if (this.refs[index] !== null) {
            this.refs[index].removeDependent(this);
        }
        this.refs[index] = ref;
        if (ref !== null) {
            ref.addDependent(this);
        }
        this.notify({ message: "ref_changed", index: index });
        this.notifyAll({ message: "dirty" });
    }

    removeDependency(dependency) {
        for (let i = 0; i < this.refs.length; i++) {
            if (this.refs[i] === dependency) {
                this.setRef(i, null);
            }
        }
    }

    get expr_status() {
        const errors = [];
        if (this.malformed_expr) {
            errors.push("malformed");
        }
        else if (this.expr === null) {
            errors.push("missing");
        }
        return errors;
    }

    get rule_status() {
        const errors = [];
        if (this.rule === null) {
            errors.push("missing");
        }
        else if (this.expr !== null && !unify(this.rule.expr, this.expr)) {
            errors.push("inapplicable");
        }
        return errors;
    }

    ref_status(i) {
        const errors = [];
        const ref = this.refs[i];
        if (ref === null) {
            errors.push("missing");
        }
        else {
            if (ref.last_number >= this.number) {
                errors.push("unreachable");
            }
            else {
                // Check that ref.context is a prefix of this.context
                for (let j = 0; j < ref.context.length; j++) {
                    if (j >= this.context.length || ref.context[j] !== this.context[j]) {
                        errors.push("unreachable");
                        break;
                    }
                }
            }
            let specs = null;
            if (this.expr !== null) {
                specs = this.rule.parts_and_subproof_specs(this.expr);
            }

            if (specs !== null) {
                const [parts_specs, subproofs_specs] = specs;
                if (i < parts_specs.length) {
                    const expr = parts_specs[i];
                    if (!(ref instanceof Line)) {
                        errors.push("wrong_type");
                    }
                    else if (ref.expr === null) {
                        errors.push("missing_expr");
                    }
                    else if (!unify(expr, ref.expr)) {
                        errors.push("wrong_expr");
                    }
                }
                else {
                    const [assumption, conclusion] = subproofs_specs[i - parts_specs.length];
                    if (!(ref instanceof Subproof)) {
                        errors.push("wrong_type");
                    }
                    else {
                        if (ref.assumption.expr === null) {
                            errors.push("missing_assumption");
                        }
                        else if (!unify(assumption, ref.assumption.expr)) {
                            errors.push("wrong_assumption");
                        }

                        if (ref.conclusion.expr === null) {
                            errors.push("missing_conclusion");
                        }
                        else if (!unify(conclusion, ref.conclusion.expr)) {
                            errors.push("wrong_conclusion");
                        }
                    }
                }
            }
        }
        return errors;
    }

    get refs_status() {
        const statuses = [];
        for (let i = 0; i < this.refs.length; i++) {
            statuses.push(this.ref_status(i));
        }
        return statuses;
    }

    get status() {
        if (this.status_cache !== null) {
            return this.status_cache;
        }

        const result = {
            expr: this.expr_status,
            rule: this.rule_status,
            refs: this.refs_status,
        }

        let ok = true;
        if (result.expr.length > 0) {
            ok = false;
        }
        if (result.rule.length > 0) {
            ok = false;
        }
        for (let i = 0; i < result.refs.length; i++) {
            if (result.refs[i].length > 0) {
                ok = false;
            }
        }

        let only_missing = true;
        if (result.expr.length > 1 || (result.expr.length > 0 && result.expr[0] !== "missing")) {
            only_missing = false;
        }
        if (result.rule.length > 1 || (result.rule.length > 0 && result.rule[0] !== "missing")) {
            only_missing = false;
        }
        for (let i = 0; i < result.refs.length; i++) {
            if (result.refs[i].length > 1 || (result.refs[i].length > 0 && result.refs[i][0] !== "missing")) {
                only_missing = false;
            }
        }

        let transitively_ok = ok;
        if (ok) {
            const parts = [];
            const subproofs = [];
            for (let i = 0; i < this.refs.length; i++) {
                const ref = this.refs[i];
                if (!ref.status.transitively_ok) {
                    transitively_ok = false;
                }
                if (ref instanceof Line) {
                    parts.push(ref.expr);
                }
                else {
                    subproofs.push([ref.assumption.expr, ref.conclusion.expr]);
                }
            }
            if (!this.rule.check(this.expr, parts, subproofs)) {
                only_missing = false;
                transitively_ok = false;
                ok = false;
            }
        }

        result.ok = ok;
        result.only_missing = only_missing;
        result.transitively_ok = transitively_ok;

        this.status_cache = result;
        return result;
    }

    get range() {
        return "" + this.number;
    }

    renumber(n, p) {
        super.renumber(n, p);
        this.root.lines[this.number] = this;
    }
}


export class Subproof extends Part {
    constructor(root, parent, position) {
        super(root, parent, position);
        this.assumption = new Line(this.root, this, 0);
        this.assumption.fixed = true;
        this.assumption.setRule(assumption);
        this.conclusion = new Line(this.root, this, 1);
        this.conclusion.fixed = true;
        this.parts = [];
        this.status_cache = null;
    }

    setDirty() {
        this.status_cache = null;
        this.parent.setDirty();
    }

    get status() {
        if (this.status_cache !== null) {
            return this.status_cache;
        }

        let ok = true;
        let only_missing = true;

        const assumption_status = this.assumption.status;
        if (!assumption_status.ok) {
            ok = false;
            if (!assumption_status.only_missing) {
                only_missing = false;
            }
        }

        const conclusion_status = this.conclusion.status;
        if (!conclusion_status.ok) {
            ok = false;
            if (!conclusion_status.only_missing) {
                only_missing = false;
            }
        }

        for (let i = 0; i < this.parts.length; i++) {
            const part_status = this.parts[i].status;
            if (!part_status.ok) {
                ok = false;
                if (!part_status.only_missing) {
                    only_missing = false;
                }
            }
        }

        let transitively_ok =
            ok &&
            this.assumption.status.transitively_ok &&
            this.conclusion.status.transitively_ok;
        
        if (transitively_ok) {
            for (let i = 0; i < this.parts.length; i++) {
                const part_status = this.parts[i].status;
                if (!part_status.transitively_ok) {
                    transitively_ok = false;
                    break;
                }
            }
        }

        const result = {
            ok: ok,
            only_missing: only_missing,
            transitively_ok: transitively_ok
        };

        this.status_cache = result;
        return result;
    }

    get size() {
        let size = 2;
        for (let i = 0; i < this.parts.length; i++) {
            size += this.parts[i].size;
        }
        return size;
    }

    _delete() {
        this.assumption._delete();
        for (let i = 0; i < this.parts.length; i++) {
            this.parts[i]._delete();
        }
        this.conclusion._delete();
        super._delete();
    }

    toJSON() {
        return {
            type: "subproof",
            assumption: this.assumption.toJSON(),
            parts: this.parts.map(part => part.toJSON()),
            conclusion: this.conclusion.toJSON(),
        };
    }

    newLine(position) {
        if (position === undefined) {
            position = this.parts.length + 1;
        }
        const line = new Line(this.root, this, position);
        this.parts.splice(position - 1, 0, line);
        this.root.renumber();
        this.setDirty();
        this.notify({ message: "line_added" });
        this.notifyAll({ message: "dirty" });
        return line;
    }

    newSubproof(position) {
        if (position === undefined) {
            position = this.parts.length + 1;
        }
        const subproof = new Subproof(this.root, this, position);
        this.parts.splice(position - 1, 0, subproof);
        this.root.renumber();
        this.setDirty();
        this.notify({ message: "subproof_added" });
        this.notifyAll({ message: "dirty" });
        return subproof;
    }

    unlinkPart(part) {
        this.setDirty();
        const index = this.parts.indexOf(part);
        if (index !== -1) {
            this.parts.splice(index, 1);
            return true;
        }
        else {
            return false;
        }
    }

    get range() {
        return this.number + "-" + (this.conclusion.number);
    }

    renumber(n, p) {
        super.renumber(n, p);
        this.assumption.renumber(n, 0);
        let m = n + 1;
        for (let i = 0; i < this.parts.length; i++) {
            this.parts[i].renumber(m, i + 1);
            m += this.parts[i].size;
        }
        this.conclusion.renumber(m, this.parts.length + 1);
        this.root.subproofs[this.range] = this;
    }

    display(indent) {
        this.assumption.display(indent + 1);
        for (let i = 0; i < this.parts.length; i++) {
            this.parts[i].display(indent + 1);
        }
        this.conclusion.display(indent + 1);
    }
}

export class Proof {

    constructor() {
        this.parts = [];
        this.number = 1;
        this.lines = {};
        this.subproofs = {};
        this.next_free_id = 1;
        this.dependents = [];
    }

    get size() {
        let size = 0;
        for (let i = 0; i < this.parts.length; i++) {
            size += this.parts[i].size;
        }
        return size;
    }

    nextId() {
        return this.next_free_id++;
    }

    setDirty() {
        // Do nothing
    }

    notify(event) {
        // Do nothing
    }

    deletePart(part) {
        const dependents = part.transitiveDependents();
        part._delete();
        this.renumber();
        dependents.forEach(dependent =>
            dependent.notify({ message: "dirty" })
        );
    }

    static fromJSON(json) {
        const proof = new Proof();

        // First pass: create all parts
        // Second pass: set all refs
        const ref_callbacks = [];

        function handle_line(line, part) {
            const expr = part.expr !== null ? parse(part.expr) : null;
            if (expr) {
                line.setExpr(expr);
            }
            const rule = rules.find(rule => rule.name === part.rule);
            if (rule) {
                line.setRule(rule);
            }
            for (let j = 0; j < part.refs.length; j++) {
                function handle_ref() {
                    if (part.refs[j] !== null) {
                        const is_range = part.refs[j].indexOf("-") !== -1;
                        if (is_range) {
                            const subproof = proof.lookupSubproof(part.refs[j]);
                            line.setRef(j, subproof);
                        }
                        else {
                            const other_line = proof.lookupLine(part.refs[j]);
                            line.setRef(j, other_line);
                        }
                    }
                }
                ref_callbacks.push(handle_ref);
            }
        }

        function handle_subproof(subproof, part) {
            handle_line(subproof.assumption, part.assumption);
            for (let i = 0; i < part.parts.length; i++) {
                const subpart = part.parts[i];
                if (subpart.type === "line") {
                    const line = subproof.newLine();
                    handle_line(line, subpart);
                }
                else {
                    const subsubproof = subproof.newSubproof();
                    handle_subproof(subsubproof, subpart);
                }
            }
            handle_line(subproof.conclusion, part.conclusion);
        }

        for (let i = 0; i < json.length; i++) {
            const part = json[i];
            if (part.type === "line") {
                const line = proof.newLine();
                handle_line(line, part);
            }
            else {
                const subproof = proof.newSubproof();
                handle_subproof(subproof, part);
            }
        }

        for (let i = 0; i < ref_callbacks.length; i++) {
            ref_callbacks[i]();
        }

        return proof;
    }
                
    toJSON() {
        return this.parts.map(part => part.toJSON());
    }

    renumber() {
        const old_lines = this.lines;
        const old_subproofs = this.subproofs;
        
        this.lines = {};
        this.subproofs = {};
        let n = this.number;
        for (let i = 0; i < this.parts.length; i++) {
            this.parts[i].renumber(n, i);
            n += this.parts[i].size;
        }

        const outdated_parts = new Set();
        const outdated_dependents = new Set();
        
        function check_changed(part) {
            if (part instanceof Line) {
                if (old_lines[part.number] !== part) {
                    outdated_parts.add(part);
                    return true;
                }
            }
            else {
                if (old_subproofs[part.range] !== part) {
                    outdated_parts.add(part);
                    return true;
                }
            }
            return false;
        }


        for (const number in old_lines) {
            const line = old_lines[number];
            if (check_changed(line)) {
                line.dependents.forEach(dependent => outdated_dependents.add(dependent));
            }
        }
        for (const range in old_subproofs) {
            const subproof = old_subproofs[range];
            if (check_changed(subproof)) {
                subproof.dependents.forEach(dependent => outdated_dependents.add(dependent));
            }
        }

        outdated_parts.forEach(part => part.notify({ message: "renumbered" }));
        outdated_dependents.forEach(dependent => dependent.notify({ message: "ref_renumbered" }));
    }

    newLine(position) {
        this.setDirty();
        if (position === undefined) {
            position = this.parts.length;
        }
        const line = new Line(this, this, position);
        this.parts.splice(position, 0, line);
        this.renumber();
        return line;
    }

    newSubproof(position) {
        this.setDirty();
        if (position === undefined) {
            position = this.parts.length;
        }
        const subproof = new Subproof(this, this);
        this.parts.splice(position, 0, subproof);
        this.renumber();
        return subproof;
    }

    unlinkPart(part) {
        this.setDirty();
        const index = this.parts.indexOf(part);
        if (index !== -1) {
            this.parts.splice(index, 1);
            return true;
        }
        else {
            return false;
        }
    }

    get_parts() {
        return this.parts;
    }

    display() {
        for (let i = 0; i < this.parts.length; i++) {
            this.parts[i].display(0);
        }
    }

    lookupPart(key) {
        if (key.indexOf("-") !== -1) {
            return this.lookupSubproof(key);
        }
        else {
            return this.lookupLine(key);
        }
    }

    lookupLine(number) {
        return this.lines[number];
    }

    lookupSubproof(range) {
        return this.subproofs[range];
    }
}


function permutations(xs) {
    if (xs.length == 0) {
        return [[]];
    }
    const res = [];
    for (let i = 0; i < xs.length; i++) {
        const ys = xs.slice();
        ys.splice(i, 1);
        const ps = permutations(ys);
        for (let j = 0; j < ps.length; j++) {
            ps[j].push(xs[i]);
            res.push(ps[j]);
        }
    }
    return res;
}

export class Rule {
    constructor(name, expr, parts, subproofs) {
        this.name = name;
        this.expr = expr;
        this.parts = parts;
        this.subproofs = subproofs;
    }

    parts_and_subproof_specs(expr) {
        const solution = unify(this.expr, expr);
        if (solution === null) {
            return null;
        }

        const parts_specs = [];
        for (let i = 0; i < this.parts.length; i++) {
            const part = substituteMetaVariables(this.parts[i], solution);
            parts_specs.push(part);
        }

        const subproofs_specs = [];
        for (let i = 0; i < this.subproofs.length; i++) {
            const assumption = substituteMetaVariables(this.subproofs[i][0], solution);
            const conclusion = substituteMetaVariables(this.subproofs[i][1], solution);
            subproofs_specs.push([assumption, conclusion]);
        }

        return [parts_specs, subproofs_specs];
    }

    check(expr, parts, subproofs) {
        if (parts.length != this.parts.length) {
            return false;
        }
        if (subproofs.length != this.subproofs.length) {
            return false;
        }

        // Gather constraints from expr
        const expr_constraints = getConstraints(this.expr, expr);
        if (expr_constraints === null) {
            return false;
        }

        // Gather possible constraints from parts
        const parts_permutations = permutations(parts);
        const parts_contraints_permutations = [];
        for (let i = 0; i < parts_permutations.length; i++) {
            const parts_constraints = [];
            for (let j = 0; j < parts_permutations[i].length; j++) {
                const part_constraints = getConstraints(this.parts[j], parts_permutations[i][j]);
                if (part_constraints === null) {
                    break;
                }
                parts_constraints.push(part_constraints);
            }
            if (parts_constraints.length == parts_permutations[i].length) {
                const all_constraints = []
                for (let j = 0; j < parts_constraints.length; j++) {
                    all_constraints.push(...parts_constraints[j]);
                }
                parts_contraints_permutations.push(all_constraints);
            }
        }

        // Gather possible constraints from subproofs
        const subproofs_permutations = permutations(subproofs);
        const subproofs_contraints_permutations = [];
        for (let i = 0; i < subproofs_permutations.length; i++) {
            const subproofs_constraints = [];
            for (let j = 0; j < subproofs_permutations[i].length; j++) {
                const assumption_constraints = getConstraints(this.subproofs[j][0], subproofs_permutations[i][j][0]);
                if (assumption_constraints === null) {
                    break;
                }
                const conclusion_constraints = getConstraints(this.subproofs[j][1], subproofs_permutations[i][j][1]);
                if (conclusion_constraints === null) {
                    break;
                }
                const subproof_constraints = assumption_constraints.concat(conclusion_constraints);
                subproofs_constraints.push(subproof_constraints);
            }
            if (subproofs_constraints.length == subproofs_permutations[i].length) {
                const all_constraints = []
                for (let j = 0; j < subproofs_constraints.length; j++) {
                    all_constraints.push(...subproofs_constraints[j]);
                }
                subproofs_contraints_permutations.push(all_constraints);
            }
        }

        // Try to solve constraints
        for (let i = 0; i < parts_contraints_permutations.length; i++) {
            for (let j = 0; j < subproofs_contraints_permutations.length; j++) {
                const all_constraints = expr_constraints.concat(parts_contraints_permutations[i]).concat(subproofs_contraints_permutations[j]);
                const solution = solveConstraints(all_constraints);
                if (solution !== null) {
                    return true;
                }
            }
        }
        return false;
    }
}

export const trueI = new Rule("trueI", constant(true), [], []);
export const falseE = new Rule("falseE", meta("1"), [constant(false)], []);
export const andI = new Rule("andI", and(meta("1"), meta("2")), [meta("1"), meta("2")], []);
export const andE1 = new Rule("andE1", meta("1"), [and(meta("1"), meta("2"))], []);
export const andE2 = new Rule("andE2", meta("2"), [and(meta("1"), meta("2"))], []);
export const orI1 = new Rule("orI1", or(meta("1"), meta("2")), [meta("1")], []);
export const orI2 = new Rule("orI2", or(meta("1"), meta("2")), [meta("2")], []);
export const orE = new Rule("orE", meta("3"), [or(meta("1"), meta("2"))], [[meta("1"), meta("3")], [meta("2"), meta("3")]]);
export const implI = new Rule("implI", implies(meta("1"), meta("2")), [], [[meta("1"), meta("2")]]);
export const implE = new Rule("implE", meta("2"), [implies(meta("1"), meta("2")), meta("1")], []);
export const notI = new Rule("notI", not(meta("1")), [], [[meta("1"), constant(false)]]);
export const notE = new Rule("notE", constant(false), [not(meta("1")), meta("1")], []);
export const iffI = new Rule("iffI", iff(meta("1"), meta("2")), [implies(meta("1"), meta("2")), implies(meta("2"), meta("1"))], []);
export const iffE1 = new Rule("iffE1", implies(meta("1"), meta("2")), [iff(meta("1"), meta("2"))], []);
export const iffE2 = new Rule("iffE2", implies(meta("2"), meta("1")), [iff(meta("1"), meta("2"))], []);
export const notNotE = new Rule("notNotE", meta("1"), [not(not(meta("1")))], []);
export const tnd = new Rule("tnd", or(meta("1"), not(meta("1"))), [], []);
export const raa = new Rule("raa", meta("1"), [], [[not(meta("1")), constant(false)]]);
export const rep = new Rule("rep", meta("1"), [meta("1")], []);
export const hypothesis = new Rule("hypothesis", meta("1"), [], []);
export const assumption = new Rule("assumption", meta("1"), [], []);

export const rules = [
    trueI,
    falseE,
    andI,
    andE1,
    andE2,
    orI1,
    orI2,
    orE,
    implI,
    implE,
    notI,
    notE,
    iffI,
    iffE1,
    iffE2,
    notNotE,
    tnd,
    raa,
    rep,
    hypothesis,
    assumption
];

export const rules_by_name = {};
for (let i = 0; i < rules.length; i++) {
    rules_by_name[rules[i].name] = rules[i];
}

export const rules_long_names = {
    "trueI": "Introduction de vrai",
    "falseE": "Élimination de faux",
    "andI": "Introduction de et",
    "andE1": "Élimination de et (1)",
    "andE2": "Élimination de et (2)",
    "orI1": "Introduction de ou (1)",
    "orI2": "Introduction de ou (2)",
    "orE": "Élimination de ou",
    "implI": "Introduction de implique",
    "implE": "Élimination de implique",
    "notI": "Introduction de non",
    "notE": "Élimination de non",
    "iffI": "Introduction de ssi",
    "iffE1": "Élimination de ssi (1)",
    "iffE2": "Élimination de ssi (2)",
    "notNotE": "Élimination de non non",
    "tnd": "Tiers exclu",
    "raa": "Raisonnement par l'absurde",
    "rep": "Répétition",
    "hypothesis": "Hypothèse",
    "assumption": "Hypothèse locale"
};