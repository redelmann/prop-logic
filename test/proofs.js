import assert from 'assert';
import { implI, implE, andI, trueI, Proof, hypothesis, rep, notI, notE } from "../src/Proof.js";
import { variable, implies, and, or, constant, not } from "../src/Expr.js";

describe("implI", function () {
    describe("check", function() {
        it("should return true in the correct case", function() {
            assert.ok(implI.check(
                implies(variable("a"), variable("b")),
                [],
                [[variable("a"), variable("b")]]
            ));

            assert.ok(implI.check(
                implies(variable("a"), and(variable("b"), variable("c"))),
                [],
                [[variable("a"), and(variable("b"), variable("c"))]]
            ));
        });

        it("should return false in the incorrect case", function() {
            assert.ok(!implI.check(
                variable("a"),
                [],
                [[variable("a"), variable("b")]]
            ));

            assert.ok(!implI.check(
                implies(variable("a"), variable("b")),
                [],
                [[variable("a"), variable("c")]]
            ));

            assert.ok(!implI.check(
                implies(variable("a"), variable("b")),
                [],
                [[variable("c"), variable("b")]]
            ));

            assert.ok(!implI.check(
                implies(variable("a"), variable("b")),
                [],
                [[variable("b"), variable("a")]]
            ));

            assert.ok(!implI.check(
                implies(variable("a"), or(variable("b"), variable("c"))),
                [],
                [[or(variable("b"), variable("c")), variable("a")]]
            ));
        });
    });
});

describe("andI", function () {
    describe("check", function() {
        it("should return true in the correct case", function() {
            assert.ok(andI.check(
                and(variable("a"), variable("b")),
                [variable("a"), variable("b")],
                []
            ));

            assert.ok(andI.check(
                and(variable("a"), variable("b")),
                [variable("b"), variable("a")],
                []
            ));
        });
    });
});

describe("Proof", function () {

    it("should work in simple case.", function() {
        const proof = new Proof();
        const subproof_1 = proof.newSubproof();
        subproof_1.assumption.setExpr(variable("a"));
        subproof_1.conclusion.setExpr(variable("a"));
        subproof_1.conclusion.setRule(rep);
        subproof_1.conclusion.setRef(0, subproof_1.assumption);
        const line_3 = proof.newLine();
        line_3.setExpr(implies(variable("a"), variable("a")));
        line_3.setRule(implI);
        line_3.setRef(0, subproof_1);
        proof.display();
    });

    it("should work in simple case.", function() {
        const proof = new Proof();
        const assumption1 = proof.newLine();
        assumption1.setExpr(implies(variable("P"), variable("Q")));
        assumption1.setRule(hypothesis);
        const assumption2 = proof.newLine();
        assumption2.setExpr(not(variable("Q")));
        assumption2.setRule(hypothesis);
        const sub3 = proof.newSubproof();
        sub3.assumption.setExpr(variable("P"));
        const line4 = sub3.newLine();
        line4.setExpr(variable("Q"));
        line4.setRule(implE);
        line4.setRef(0, assumption1);
        line4.setRef(1, sub3.assumption);
        sub3.conclusion.setExpr(constant(true));
        sub3.conclusion.setRule(notE);
        sub3.conclusion.setRef(0, assumption2);
        sub3.conclusion.setRef(1, line4);
        const line6 = proof.newLine();
        line6.setExpr(not(variable("P")));
        line6.setRule(notI);
        line6.setRef(0, sub3);
        const line7 = proof.newLine();
        line7.addListener(function(event_name) {
            console.log("EVENT", event_name);
        });
        line7.setExpr(implies(variable("P"), constant(false)));
        line7.setRule(implI);
        line7.setRef(0, sub3);
        sub3.conclusion.setExpr(constant(false));
        proof.display();
        proof.deletePart(line6);
        proof.display();
        proof.deletePart(line4);
        proof.display();
    });
});