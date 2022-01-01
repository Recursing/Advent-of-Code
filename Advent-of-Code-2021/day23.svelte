<script lang="typescript">
  // See https://svelte.dev/repl/8c6916ff6a764cd78c131fe2426f090c?version=3.44.3
  import _ from "lodash";
  import {
    initialStatePart1,
    initialStatePart2,
    afterMove,
    isLetter,
    directions,
    Direction,
  } from "./day23";

  let part2 = false;
  $: state = part2 ? initialStatePart2 : initialStatePart1;

  let history: typeof state[] = [];
  let selectedCoord: number | undefined = undefined;

  function showMove(direction: Direction) {
    if (state.grid[selectedCoord + direction] !== "·") {
      return;
    }
    history.push(_.cloneDeep(state));
    state = afterMove(state, selectedCoord, direction);
    selectedCoord = state.lastMovedCoord;
  }

  function handleClick(coord: number) {
    if (isLetter(state.grid[coord])) {
      selectedCoord = coord;
    } else if (
      state.grid[coord] == "·" &&
      directions.includes((coord - selectedCoord) as Direction)
    ) {
      showMove((coord - selectedCoord) as Direction);
    }
  }

  function undo() {
    if (history.length > 0) {
      state = history.pop();
      selectedCoord = state.lastMovedCoord;
    }
  }

  function handleKey(key: KeyboardEvent) {
    const pressedKey = key.key.toUpperCase();

    if (isLetter(pressedKey)) {
      const indexes = [...state.grid]
        .map((v, i) => (v === pressedKey ? i : null))
        .filter((i) => i !== null);
      selectedCoord =
        indexes[(indexes.indexOf(selectedCoord) + 1) % indexes.length];
    } else if (pressedKey === "BACKSPACE") {
      undo();
      return;
    }
    if (!isLetter(state.grid[selectedCoord])) {
      return;
    }
    if (pressedKey === "ARROWUP") {
      showMove(-14);
      return;
    }
    if (pressedKey === "ARROWDOWN") {
      showMove(14);
      return;
    }
    if (pressedKey === "ARROWLEFT") {
      showMove(-1);
      return;
    }
    if (pressedKey === "ARROWRIGHT") {
      showMove(1);
      return;
    }
  }
</script>

<svelte:window on:keydown={handleKey} />
<main>
  <div class="head">
    <p>
      Cost: {(state.cost + "").padStart(5, "0")} (Best: {part2 ? 46451 : 10321})
    </p>
    <button on:click={undo}>Undo</button>
    <button
      on:click={() => {
        part2 = !part2;
        selectedCoord = undefined;
      }}>Part {part2 ? 1 : 2}</button
    >
  </div>

  <div class="grid">
    {#each state.grid as cell, i}
      <div
        class="cell"
        class:selected={i === selectedCoord}
        class:wall={state.grid[i] === "#"}
        class:space={state.grid[i] === "·"}
        on:click={() => handleClick(i)}
      >
        {cell}
      </div>
    {/each}
  </div>
</main>

<style>
  main {
    display: flex;
    flex-direction: column;
    height: 100%;
  }
  .wall {
    background-color: rgb(100, 100, 255);
  }
  .space {
    opacity: 0.5;
  }
  .grid {
    max-width: 100%;
    display: grid;
    grid: auto / repeat(14, 1fr);
  }

  .cell {
    max-width: 10vmin;
    aspect-ratio: 1;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 5vmin;
  }
  .head {
    display: flex;
    justify-content: center;
    gap: 1rem;
  }

  .selected {
    background-color: green;
    color: red;
  }
</style>
