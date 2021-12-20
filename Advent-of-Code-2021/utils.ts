import { assert } from "https://deno.land/std@0.117.0/testing/asserts.ts";

// built-ins I miss from python
// don't want to import lodash but maybe I should, it has everything here

export function sum(array: number[]): number {
  return array.reduce<number>((a, b) => a + b, 0);
}

export function count<T>(
  array: Array<T>,
  condition: (arg0: T, index: number) => boolean,
): number {
  return array.filter(condition).length;
}

export function range(
  start: number,
  end?: number,
  inclusive = false,
): number[] {
  if (end === undefined) {
    end = start;
    start = 0;
  }
  let length = Math.abs(end - start);
  if (inclusive) {
    length += 1;
  }
  return [...Array(length).keys()].map((index) =>
    end! > start ? start + index : start - index
  );
}

export function zip<T extends unknown[][]>(
  ...args: T
): { [K in keyof T]: T[K] extends (infer V)[] ? V : never }[] {
  const minLength = Math.min(...args.map((arr) => arr.length));
  // @ts-expect-error This is too much for ts
  return range(minLength).map((i) => args.map((arr) => arr[i]));
}

export function readDay(n: number): string[] {
  const paddedN = String(n).padStart(2, "0");
  return Deno.readTextFileSync(`./day${paddedN}.txt`).split("\n");
}

export function isIn<T1 extends T2, T2>(
  array: Readonly<T1[]>,
  value: T2,
): value is T1 {
  return array.includes(value as T1);
}

export class Vec {
  constructor(public readonly values: number[]) {}

  public add(other: Vec) {
    return new Vec(zip(this.values, other.values).map(([a, b]) => a + b));
  }

  public static zeros(length: number) {
    return new Vec(range(length).map(() => 0));
  }
}

export function chunks<T>(arr: T[], size: number): T[][] {
  assert(Number.isInteger(arr.length / size));
  return range(arr.length / size).map((i) =>
    range(size).map((j) => arr[i * size + j])
  );
}

export type DeepReadonly<T> = {
  readonly [P in keyof T]: DeepReadonly<T[P]>;
};

export function product<T1, T2>(arr1: T1[], arr2: T2[]): [T1, T2][] {
  return arr1.flatMap((val1) => arr2.map((val2): [T1, T2] => [val1, val2]));
}

export function neighbors(
  y: number,
  x: number,
  height: number,
  width: number,
): [number, number][] {
  return [[-1, 0], [1, 0], [0, -1], [0, 1]]
    .map(([dy, dx]): [number, number] => [y + dy, x + dx])
    .filter(([ny, nx]) => 0 <= ny && ny < height && 0 <= nx && nx < width);
}

export function repeat<T>(arr: T[], times: number): T[] {
  return range(times).flatMap(() => arr);
}

export function pairs<T>(arr: T[]): [T, T][] {
  const ret: [T, T][] = [];
  for (let i = 0; i < arr.length; i++) {
    for (let j = i + 1; j < arr.length; j++) {
      ret.push([arr[i], arr[j]]);
    }
  }
  return ret;
}

export type Replace<OriginalType, Keys extends keyof OriginalType, NewType> =
  & Omit<OriginalType, Keys>
  & { [K in Keys]: NewType };
