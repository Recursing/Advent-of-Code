import { assert } from "https://deno.land/std@0.117.0/testing/asserts.ts";

// built-ins I miss from python
// don't want to import lodash but maybe I should, it has everything here

export function sum(array: number[]): number {
  return array.reduce<number>((a, b) => a + b, 0);
}

export function count<T>(
  array: Array<T>,
  condition: (arg0: T, index: number) => boolean
): number {
  return array.filter(condition).length;
}

export function range(end: number): number[] {
  return [...Array(end).keys()];
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
  value: T2
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
