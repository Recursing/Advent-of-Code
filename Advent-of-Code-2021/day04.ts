import * as utils from "./utils.ts";

const lines = utils.readDay(4);
const numbers: Readonly<string[]> = lines.shift()!.split(",");

const tables: utils.DeepReadonly<string[][][]> = utils.chunks(
  lines.filter((line) => line).map((line) => line.trim().split(/\s+/)),
  5
);
const uncalledNumbers: string[][][] = structuredClone(tables);

const rowsCounts = tables.map(() => utils.range(5).map(() => 0));
const columnCounts: number[][] = structuredClone(rowsCounts);

const numbersIndex: { [K in string]: [number, number, number][] } = {};
tables.forEach((table, tableIndex) =>
  table.forEach((row, rowIndex) =>
    row.forEach((value, colIndex) => {
      if (numbersIndex[value] === undefined) numbersIndex[value] = [];
      numbersIndex[value].push([tableIndex, rowIndex, colIndex]);
    })
  )
);
let winningNumber: string;
let winningUncalledNumbers: number[];
let losingNumber: string;
let losingUncalledNumbers: number[];
const wonTables: Set<number> = new Set();

numbers.forEach((number) => {
  numbersIndex[number].forEach(([table, row, col]) => {
    if (wonTables.has(table)) {
      return;
    }
    rowsCounts[table][row] += 1;
    columnCounts[table][col] += 1;
    uncalledNumbers[table][row][col] = "";
    if (rowsCounts[table][row] == 5 || columnCounts[table][col] == 5) {
      if (winningNumber === undefined) {
        winningNumber = number;
        winningUncalledNumbers = uncalledNumbers[table].flat().map(Number);
      }
      losingNumber = number;
      losingUncalledNumbers = uncalledNumbers[table].flat().map(Number);
      wonTables.add(table);
    }
  });
});
console.log(utils.sum(winningUncalledNumbers!) * Number(winningNumber!));
console.log(utils.sum(losingUncalledNumbers!) * Number(losingNumber!));
