import * as utils from "./utils.ts";

const nums = (await utils.readDay(1)).map((line) => parseInt(line, 10));
let pairs = utils.zip(nums, nums.slice(1));
console.log(utils.sum(pairs.map(([a, b]) => a < b)));
pairs = utils.zip(nums, nums.slice(3));
console.log(utils.sum(pairs.map(([a, b]) => a < b)));
