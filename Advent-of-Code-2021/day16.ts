import { assert } from "https://deno.land/std@0.117.0/testing/asserts.ts";
import * as utils from "./utils.ts";

const IDS = [0, 1, 2, 3, 4, 5, 6, 7] as const;

type LiteralPacket = {
  version: number;
  typeID: 4;
  value: number;
};
type OperatorPacket = {
  version: number;
  typeID: Exclude<(typeof IDS)[number], 4>;
  subpackets: Readonly<Packet[]>;
};
type Packet = OperatorPacket | LiteralPacket;

function parseValue(bits: string[]): number {
  let number = 0;
  let sentinelBit = "1";
  do {
    sentinelBit = bits.shift()!;
    const digits = bits.splice(0, 4);
    number = number * 16 + parseInt(digits.join(""), 2);
  } while (sentinelBit === "1");
  return number;
}

function parseAllPackets(
  bits: string[],
  maxPackets = Infinity,
): Readonly<Packet[]> {
  const packets: Packet[] = [];
  while (bits.length > 8 && packets.length < maxPackets) {
    const version = parseInt(bits.splice(0, 3).join(""), 2);
    const typeID = parseInt(bits.splice(0, 3).join(""), 2);
    if (!utils.isIn(IDS, typeID)) {
      throw Error();
    }
    if (typeID == 4) {
      const value = parseValue(bits);
      packets.push({ version, typeID, value });
      continue;
    }
    const lengthType = bits.shift()!;
    if (lengthType == "0") {
      const packetsLength = parseInt(bits.splice(0, 15).join(""), 2);
      const subpackets = parseAllPackets(bits.splice(0, packetsLength));
      packets.push({ version, typeID, subpackets });
      continue;
    }
    const packetsNumber = parseInt(bits.splice(0, 11).join(""), 2);
    const subpackets = parseAllPackets(bits, packetsNumber);
    packets.push({ version, typeID, subpackets });
    continue;
  }
  return packets;
}
const bits = [
  ...utils.readDay(16)[0],
].map((d) => ({
  "0": "0000",
  "1": "0001",
  "2": "0010",
  "3": "0011",
  "4": "0100",
  "5": "0101",
  "6": "0110",
  "7": "0111",
  "8": "1000",
  "9": "1001",
  "A": "1010",
  "B": "1011",
  "C": "1100",
  "D": "1101",
  "E": "1110",
  "F": "1111",
}[d])).join("");
const packets = parseAllPackets([...bits]);
assert(packets.length == 1);
function sumVersions(packet: Packet): number {
  if (packet.typeID == 4) {
    return packet.version;
  }
  return packet.version + utils.sum(packet.subpackets.map(sumVersions));
}
console.log(sumVersions(packets[0]));

function evalPacket(packet: Packet): number {
  if (packet.typeID == 4) {
    return packet.value;
  }
  const childrenValues = packet.subpackets.map(evalPacket);
  switch (packet.typeID) {
    case 0:
      return utils.sum(childrenValues);
    case 1:
      return childrenValues.reduce((a, b) => a * b, 1);
    case 2:
      return Math.min(...childrenValues);
    case 3:
      return Math.max(...childrenValues);
    case 5:
      return +(childrenValues[0] > childrenValues[1]);
    case 6:
      return +(childrenValues[0] < childrenValues[1]);
    case 7:
      return +(childrenValues[0] == childrenValues[1]);
  }
}
console.log(evalPacket(packets[0]));
