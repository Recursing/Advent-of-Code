import * as utils from "./utils.ts";

const nums = utils.readDay(1).map(Number);
let pairs = utils.zip(nums, nums.slice(1));
console.log(utils.count(pairs, ([a, b]) => a < b));
pairs = utils.zip(nums, nums.slice(3));
console.log(utils.count(pairs, ([a, b]) => a < b));

// More idiomatic implementation, comparison with undefined is always false
// so no need to do `value > (nums[index - 1] ?? Infinity)`
console.log(utils.count(nums, (value, index) => value > nums[index - 1]));
console.log(utils.count(nums, (value, index) => value > nums[index - 3]));
