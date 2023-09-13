import { MetaVariable, Not, exprEqual } from "./Expr.js";

export function getConstraints(left, right) {
    if (left.kind === MetaVariable) {
      return [[left, right]];
    }
    if (right.kind === MetaVariable) {
      return [[right, left]];
    }
    if (left.kind !== right.kind) {
      return null;
    }
    switch (left.kind) {
      case "Variable":
        if (left.name === right.name) {
          return [];
        }
        return null;
      case "Constant":
        if (left.value === right.value) {
          return [];
        }
        return null;
      case "Not":
        return getConstraints(left.inner, right.inner);
      default:
        const left_constraints = getConstraints(left.left, right.left);
        if (left_constraints === null) {
          return null;
        }
        const right_constraints = getConstraints(left.right, right.right);
        if (right_constraints === null) {
          return null;
        }
        return left_constraints.concat(right_constraints);
    }
  }
  
  export function substituteMetaVariables(expr, substitutions) {
    switch (expr.kind) {
      case "MetaVariable":
        if (expr.name in substitutions) {
          return substitutions[expr.name];
        }
        return expr;
      case "Variable":
        return expr;
      case "Constant":
        return expr;
      case "Not":
        return { kind: Not, inner: substituteMetaVariables(expr.inner, substitutions) };
      default:
        return {
          kind: expr.kind,
          left: substituteMetaVariables(expr.left, substitutions),
          right: substituteMetaVariables(expr.right, substitutions)
        };
    }
  }
  
  function metaVariableOccursIn(expr, name) {
    switch (expr.kind) {
      case "MetaVariable":
        return expr.name === name;
      case "Variable":
        return false;
      case "Constant":
        return false;
      case "Not":
        return metaVariableOccursIn(expr.inner, name);
      default:
        return metaVariableOccursIn(expr.left, name) ||
               metaVariableOccursIn(expr.right, name);
    }
  }
  
  export function solveConstraints(constraints) {
    const solution = {};
    constraints = constraints.slice();
    while (constraints.length > 0) {
      const constraint = constraints.pop();
      if (exprEqual(constraint[0], constraint[1])) {
        continue;
      }
      if (constraint[0].kind === MetaVariable) {
        if (metaVariableOccursIn(constraint[1], constraint[0].name)) {
          return null;
        }
        const substs = { [constraint[0].name]: constraint[1] }
        for (let i = 0; i < constraints.length; i++) {
          constraints[i] = 
            [ substituteMetaVariables(constraints[i][0], substs),
              substituteMetaVariables(constraints[i][1], substs) ];
        }
        for (const name in solution) {
          solution[name] = substituteMetaVariables(solution[name], substs);
        }
        solution[constraint[0].name] = constraint[1];
      }
      else if (constraint[1].kind === MetaVariable) {
        constraints.push([constraint[1], constraint[0]]);
      }
      else {
        const extra_constraints = getConstraints(constraint[0], constraint[1]);
        if (extra_constraints === null) {
          return null;
        }
        constraints.push(...extra_constraints);
      }
    }
    return solution;
  }

  export function unify(expr1, expr2) {
    const constraints = getConstraints(expr1, expr2);
    if (constraints === null) {
      return null;
    }
    return solveConstraints(constraints);
  }