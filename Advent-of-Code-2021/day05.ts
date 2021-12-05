import { assert } from "https://deno.land/std@0.117.0/testing/asserts.ts";
import * as utils from "./utils.ts";

const lines: number[][] = utils.readDay(5).map((line) =>
  line
    .split(" -> ")
    .flatMap((point) => point.split(","))
    .map(Number)
);

const maxCoordinate = Math.max(...lines.flat());
const hits = utils
  .range(maxCoordinate + 1)
  .map(() => utils.range(maxCoordinate + 1).map(() => 0));

const straightLines = lines.filter(([x1, y1, x2, y2]) => x1 == x2 || y1 == y2);
straightLines.forEach(([x1, y1, x2, y2]) =>
  utils
    .product(utils.range(x1, x2, true), utils.range(y1, y2, true))
    .forEach(([x, y]) => (hits[y][x] += 1))
);
console.log(hits.flat().filter((v) => v >= 2).length);

assert(
  lines.every(
    ([x1, y1, x2, y2]) =>
      x1 == x2 || y1 == y2 || Math.abs(x1 - x2) == Math.abs(y1 - y2)
  )
);

const diagonalLines = lines.filter(([x1, y1, x2, y2]) => x1 != x2 && y1 != y2);
assert(lines.length === diagonalLines.length + straightLines.length);

diagonalLines.forEach(([x1, y1, x2, y2]) =>
  utils
    .zip(utils.range(x1, x2, true), utils.range(y1, y2, true))
    .forEach(([x, y]) => (hits[y][x] += 1))
);
console.log(hits.flat().filter((v) => v >= 2).length);
