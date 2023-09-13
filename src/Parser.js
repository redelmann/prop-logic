// Copyright 2022 Romain Edelmann
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


import { constant, ands, nands, ors, nors, xors, impliess, iffs, not, variable } from './Expr.js';
import { tokenize } from './Tokenizer.js';

export class ParseError extends Error {
  constructor(code, ...params) {
    super(params);

    if(Error.captureStackTrace) {
      Error.captureStackTrace(this, ParseError);
    }
    this.name = 'ParseError';
    this.code = code;
  }
}

export function parse(input) {
  if (typeof input === 'string') {
    input = tokenize(input);
  }

  const tokens = input.filter(token => token.tag != "SPACE");

  function consume(tag) {
    if (tokens.length > 0 && tokens[0].tag === tag) {
      return tokens.shift();
    }
    return null;
  }

  function parseLiteral() {
    if (consume("TRUE")) {
      return constant(true);
    }
    if (consume("FALSE")) {
      return constant(false);
    }
    let token = consume("META");
    if (token) {
      return variable(token.content.slice(1));
    }
    token = consume("ID");
    if (token) {
      return variable(token.content);
    }
    return null;
  }

  function parseAtom() {
    const res = parseLiteral() || parseExprWithParentheses();
    if (!res) {
      throw new ParseError("EXPECTED_ATOM");
    }
    return res;
  }

  function parseNegation() {
    let n = 0;
    while (consume("NOT")) {
      n++;
    }
    let res = parseAtom();
    for(let i = 0; i < n; i++) {
      res = not(res);
    }
    return res;
  }

  function parseBinary(op, below, constr) {
    const exprs = [];
    exprs.push(below());
    while (consume(op)) {
      exprs.push(below());
    }
    return constr(exprs);
  }

  function parseNegConjunction() {
    return parseBinary("NAND", parseNegation, nands);
  }

  function parseConjunction() {
    return parseBinary("AND", parseNegConjunction, ands);
  }

  function parseXor() {
    return parseBinary("XOR", parseConjunction, xors); 
  }

  function parseNegDisjunction() {
    return parseBinary("NOR", parseXor, nors);
  }

  function parseDisjunction() {
    return parseBinary("OR", parseNegDisjunction, ors);
  }

  function parseImplication() {
    return parseBinary("IMPLIES", parseDisjunction, impliess);
  }

  function parseExpr() {
    return parseBinary("IFF", parseImplication, iffs);
  }

  function parseExprWithParentheses() {
    if (consume("OPEN")) {
      const expr = parseExpr();
      if (!consume("CLOSE")) {
        throw new ParseError("CLOSE_PARENS");
      }
      return expr;
    }
  }

  const expr = parseExpr();
  if (tokens.length > 0) {
    throw new ParseError("EXTRA_TOKENS");
  }
  return expr;
}