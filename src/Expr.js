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


export const MetaVariable = "MetaVariable";
export const Variable = "Variable";
export const Constant = "Constant";
export const And = "And";
export const Nand = "Nand";
export const Or = "Or";
export const Nor = "Nor";
export const Xor = "Xor";
export const Implies = "Implies";
export const Not = "Not";
export const Iff = "Iff";      

export function exprEqual(left, right) {
  if (left.kind !== right.kind) {
  return false;
  }
  switch (left.kind) {
  case "Variable":
  return left.name === right.name;
  case "Constant":
  return left.value === right.value;
  case "Not":
  return exprEqual(left.inner, right.inner);
  default:
  return exprEqual(left.left, right.left) &&
      exprEqual(left.right, right.right);
  }
}


export function meta(name) {
  return { kind: MetaVariable, name: name };
}

export function variable(name) {
  return { kind: Variable, name: name };
}

export function constant(value) {
  return { kind: Constant, value: value };
}

export function nand(left, right) {
  return { kind: Nand, left: left, right: right };
}

export function nands(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("nands: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(nand(left, right));
  }
  return es[0];
}

export function and(left, right) {
  return { kind: And, left: left, right: right };
}

export function ands(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("ands: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(and(left, right));
  }
  return es[0];
}

export function nor(left, right) {
  return { kind: Nor, left: left, right: right };
}

export function nors(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("nors: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(nor(left, right));
  }
  return es[0];
}

export function or(left, right) {
  return { kind: Or, left: left, right: right };
}

export function ors(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("ors: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(or(left, right));
  }
  return es[0];
}

export function xor(left, right) {
  return { kind: Xor, left: left, right: right };
}

export function xors(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("xors: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(xor(left, right));
  }
  return es[0];
}

export function implies(left, right) {
  return { kind: Implies, left: left, right: right };
}

export function impliess(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("ors: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(implies(left, right));
  }
  return es[0];
}

export function iff(left, right) {
  return { kind: Iff, left: left, right: right };
}

export function iffs(exprs) {
  const es = exprs.slice();
  if (es.length == 0) {
    throw new Error("iffs: exprs is empty.");
  }
  while (es.length > 1) {
    const right = es.pop();
    const left = es.pop();
    es.push(iff(left, right));
  }
  return es[0];
}

export function not(expr) {
  return { kind: Not, inner: expr };
}

export function freeVariables(expression) {
  const vars = new Set([]);

  function go(expr) {
  switch(expr.kind) {
  case "Variable":
    vars.add(expr.name);
    break;
  case "Constant":
    break;
  case "Not":
    go(expr.inner);
    break;
  default:
    go(expr.left);
    go(expr.right);
    break;
  }
  }

  go(expression);
  return Array.from(vars).sort();
}

export function exprToString(expression) {

  function iffToString(expr) {
    if (expr.kind == "Iff") {
      return impliesToString(expr.left) + " ssi " + iffToString(expr.right);
    }
    else {
      return impliesToString(expr)
    }
  }
  
  function impliesToString(expr) {
    if (expr.kind == "Implies") {
      return orToString(expr.left) + " implique " + impliesToString(expr.right);
    }
    else {
      return orToString(expr)
    }
  }
  
  function orToString(expr) {
    if (expr.kind == "Or") {
      return norToString(expr.left) + " ou " + orToString(expr.right);
    }
    else {
      return norToString(expr)
    }
  }

  function norToString(expr) {
    if (expr.kind == "Nor") {
      return xorToString(expr.left) + " non-ou " + norToString(expr.right);
    }
    else {
      return xorToString(expr)
    }
  }

  function xorToString(expr) {
    if (expr.kind == "Xor") {
      return andToString(expr.left) + " ou-x " + xorToString(expr.right);
    }
    else {
      return andToString(expr)
    }
  }
  
  function andToString(expr) {
    if (expr.kind == "And") {
      return nandToString(expr.left) + " et " + andToString(expr.right);
    }
    else {
      return nandToString(expr)
    }
  }

  function nandToString(expr) {
    if (expr.kind == "Nand") {
      return notToString(expr.left) + " non-et " + nandToString(expr.right);
    }
    else {
      return notToString(expr)
    }
  }
  
  function notToString(expr) {
    if (expr.kind == "Not") {
      return "non " + notToString(expr.inner);
    }
    else {
      return atomicToString(expr);
    }
  }
  
  function atomicToString(expr) {
    if (expr.kind == "Constant") {
      return expr.value ? "vrai" : "faux";
    }
    else if (expr.kind == "Variable") {
      return expr.name;
    }
    else if (expr.kind == "MetaVariable") {
      return "?" + expr.name;
    }
    else {
      return "(" + iffToString(expr) + ")";
    }
  }

  return iffToString(expression);
}

export function verboseExprToString(expression, parens) {
  function go(expr) {
    if (expr.kind == "Variable") {
      return expr.name;
    }
    if (expr.kind == "Constant") {
      return expr.value ? "vrai" : "faux";
    }
    const pre = parens ? "(" : "";
    const post = parens ? ")" : "";

    if (expr.kind == "Not") {
      return pre + "non " + verboseExprToString(expr.inner, true) + post;
    }

    let op;
    switch (expr.kind) {
      case "And": {
        op = "et";
        break;
      }
      case "Nand": {
        op = "non-et";
        break;
      }
      case "Or": {
        op = "ou";
        break;
      }
      case "Nor": {
        op = "non-ou";
        break;
      }
      case "Xor": {
        op = "ou-x";
        break;
      }
      case "Implies": {
        op = "implique";
        break;
      }
      case "Iff": {
        op = "ssi";
        break;
      }
    }
    
    return pre +
      verboseExprToString(expr.left, true) + " " + op + " " + 
      verboseExprToString(expr.right, expr.right.kind !== expr.kind && expr.right.kind !== "Not") + post;
  }

  return go(expression, false);
}

export function evaluate(expr, interpretation) {
  switch (expr.kind) {
    case "Variable":
      return interpretation[expr.name];
    case "Constant":
      return expr.value;
    case "Not":
      return !evaluate(expr.inner, interpretation);
    case "And":
      return evaluate(expr.left, interpretation) && evaluate(expr.right, interpretation);
    case "Nand":
      return !(evaluate(expr.left, interpretation) && evaluate(expr.right, interpretation));
    case "Or":
      return evaluate(expr.left, interpretation) || evaluate(expr.right, interpretation);
    case "Nor":
      return !(evaluate(expr.left, interpretation) || evaluate(expr.right, interpretation));
    case "Xor":
      return evaluate(expr.left, interpretation) !== evaluate(expr.right, interpretation);
    case "Implies":
      return !evaluate(expr.left, interpretation) || evaluate(expr.right, interpretation);
    case "Iff":
      return evaluate(expr.left, interpretation) === evaluate(expr.right, interpretation);
  }
}

export function interpretations(variables) {
  const interpretations = [];
  for (let i = 0; i < Math.pow(2, variables.length); i++) {
    const interpretation = {};
    for (let j = 0; j < variables.length; j++) {
      interpretation[variables[j]] = ((i >> (variables.length - 1 - j)) & 1) === 1;
    }
    interpretations.push(interpretation);
  }
  return interpretations;
}