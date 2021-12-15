import * as utils from "./utils.ts";

const grid: number[][] = utils.readDay(15).map((line) =>
    [...line].map(Number)
);

function solve(grid: number[][]) {
    const distances = grid.map((row) => row.map(() => Infinity));
    distances[0][0] = 0;
    const height = grid.length;
    const width = grid[0].length;

    const frontier: [number, number][] = [[0, 0]];
    while (frontier.length) {
        // One day let's write a priority queue, and maybe use A*
        const [y, x] = frontier
            .sort(([y1, x1], [y2, x2]) => distances[y2][x2] - distances[y1][x1])
            .pop()!;
        for (const [ny, nx] of utils.neighbors(y, x, height, width)) {
            if (distances[ny][nx] > grid[ny][nx] + distances[y][x]) {
                distances[ny][nx] = grid[ny][nx] + distances[y][x];
                frontier.push([ny, nx]);
            }
        }
    }
    return distances[height - 1][width - 1];
}
console.log(solve(grid));

const bigGrid = utils.range(5)
    .flatMap((i) => grid.map(row => utils.range(5)
        .flatMap((j) => row.map((n) => (n + i + j - 1) % 9 + 1))));
console.log(solve(bigGrid));