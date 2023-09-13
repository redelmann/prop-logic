
import assert from 'assert';
import { exprEqual, and, variable } from '../src/Expr.js';
import { parse } from '../src/Parser.js';


describe('parse', function() {
    it('should parse a simple expression', function() {
        assert.ok(exprEqual(
            parse("a et b"),
            and(variable("a"), variable("b")),
        ));
    });
});
