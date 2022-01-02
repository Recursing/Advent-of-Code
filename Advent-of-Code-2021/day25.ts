import * as _ from "./utils.ts";
const grid = (_.readDay(25)).map((l) => [...l]);
const ROWS = grid.length;
const COLS = grid[0].length;
let moved = true;
let i;
for (i = 1; i < 1_000_000 && moved; i++) {
  moved = false;
  let oldGrid = structuredClone(grid);
  const alreadySet: Set<string> = new Set();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (alreadySet.has(`${r}x${c}`)) {
        continue;
      }
      const nc = (c + 1) % COLS;
      if (grid[r][c] === ">" && oldGrid[r][nc] === ".") {
        grid[r][c] = ".";
        grid[r][nc] = ">";
        alreadySet.add(`${r}x${nc}`);
        moved = true;
      }
    }
  }
  alreadySet.clear();
  oldGrid = structuredClone(grid);
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (alreadySet.has(`${r}x${c}`)) {
        continue;
      }
      const nr = (r + 1) % ROWS;
      if (grid[r][c] === "v" && oldGrid[nr][c] === ".") {
        grid[r][c] = ".";
        grid[nr][c] = "v";
        alreadySet.add(`${nr}x${c}`);
        moved = true;
      }
    }
  }
}
console.log(i);
