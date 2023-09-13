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


import Logic from 'logic-solver';

import { not } from './Expr.js';

function exprToLogic(expr) {
  switch (expr.kind) {
    case "Variable": {
      return expr.name;
    }
    case "Constant": {
      return expr.value ? Logic.TRUE : Logic.FALSE;
    }
    case "And": {
      return Logic.and(exprToLogic(expr.left), exprToLogic(expr.right));
    }
    case "Nand": {
      return Logic.not(Logic.and(exprToLogic(expr.left), exprToLogic(expr.right)));
    }
    case "Or": {
      return Logic.or(exprToLogic(expr.left), exprToLogic(expr.right));
    }
    case "Nor": {
      return Logic.not(Logic.or(exprToLogic(expr.left), exprToLogic(expr.right)));
    }
    case "Xor": {
      return Logic.xor(exprToLogic(expr.left), exprToLogic(expr.right));
    }
    case "Implies": {
      return Logic.implies(exprToLogic(expr.left), exprToLogic(expr.right));
    }
    case "Iff": {
      return Logic.equiv(exprToLogic(expr.left), exprToLogic(expr.right));
    }
    case "Not": {
      return Logic.not(exprToLogic(expr.inner));
    }
    default: {
      return null;
    }
  }
}

export function getModel(expr) {
  const solver = new Logic.Solver();
  solver.require(exprToLogic(expr));
  const solution = solver.solve();
  if (solution === null) {
    return null;
  }
  else {
    return solution.getMap();
  }
}

export function getAllModels(expr, n) {
  if (n === undefined) {
    n = -1;
  }
  const solver = new Logic.Solver();
  solver.require(exprToLogic(expr));
  const solutions = [];
  let solution = null; 
  while ((solution = solver.solve()) !== null && (n === -1 || solutions.length < n)) {
    solutions.push(solution.getMap());
    solver.forbid(solution.getFormula());
  }
  return solutions;
}

export function getCounterExample(expr) {
  return getModel(not(expr));
}
