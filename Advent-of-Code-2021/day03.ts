import * as utils from "./utils.ts";

const lines = await utils.readDay(3);
const numbers: Readonly<number[][]> = lines.map((line) =>
  [...line].map(Number)
);
const BIT_LENGTH = numbers[0].length;
function bitsToInt(bits: number[]): number {
  return parseInt(bits.join(""), 2);
}
const mostCommonValues = numbers
  .map((value) => new utils.Vec(value))
  .reduce((vec, acc) => acc.add(vec), utils.Vec.zeros(BIT_LENGTH))
  .values.map((total) => total >= numbers.length / 2)
  .map(Number);
const leastCommonValues = mostCommonValues.map((v) => 1 - v);
console.log(bitsToInt(mostCommonValues) * bitsToInt(leastCommonValues));

function findRating(keepLeastCommon: boolean) {
  let values = numbers;
  for (const index of utils.range(BIT_LENGTH)) {
    const counts = utils.sum(values.map((number) => number[index]));
    let target = +(counts >= values.length / 2);
    if (keepLeastCommon) {
      target = 1 - target;
    }
    values = values.filter((number) => number[index] === target);
    if (values.length === 1) {
      return values[0];
    }
  }
  throw Error();
}

console.log(bitsToInt(findRating(false)) * bitsToInt(findRating(true)));
