script;

use std::assert::{assert, require};
use std::constants::ZERO;
use std::chain::log_b256;

fn main() -> bool {
    let a: b256 = 0b1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001_1000000000000001;

    let b: b256 = 0b0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001_0000000100000001;

    let c: b256 = 0b0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001;

    let d: b256 = 0b1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000_1000000100000000;

    let e: b256 = 0b1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001_1000000100000001;

    let f: b256 = 0b1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000;

    let g: b256 = 0b0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000_0000000100000000;

    //0001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001
    let b256_1: b256 = 0x1111111111111111111111111111111111111111111111111111111111111111;

    // 0010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010
    let b256_2: b256 = 0x2222222222222222222222222222222222222222222222222222222222222222;

    //0011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011
    let b256_3: b256 = 0x3333333333333333333333333333333333333333333333333333333333333333;

    // 0100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100
    let b256_4: b256 = 0x4444444444444444444444444444444444444444444444444444444444444444;

    // 0101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101
    let b256_5: b256 = 0x5555555555555555555555555555555555555555555555555555555555555555;
    let b256_F: b256 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

    ///////////////////////////////////////////////////////
    // test &, |, ^
    ///////////////////////////////////////////////////////

    assert(a & b == c);
    assert(a & c == c);
    assert(b & c == c);
    assert(a & d == f);
    assert(f & e == f);
    assert(b & d == g);
    assert(b256_F & b256_3 == b256_3);
    assert(b256_1 & b256_2 == ZERO);
    assert(b256_F & b256_2 == b256_2);

    assert(a | g == e);
    assert(a | d == e);
    assert(a | c == a);
    assert(c | f == a);
    assert(c | d == e);
    assert(b256_1 | b256_2 == b256_3);
    assert(b256_1 | b256_4 == b256_5);
    assert(b256_2 | b256_3 == b256_3);

    assert(a ^ b == d);
    assert(a ^ g == e);
    assert(b ^ d == a);
    assert(f ^ g == d);
    assert(b256_1 ^ b256_2 == b256_3);
    assert(b256_2 ^ b256_3 == b256_1);
    assert(b256_1 ^ b256_3 == b256_2);

    let one: b256 = 0b0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000001;
    let two: b256 = 0b0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000010;

    let g: b256 = 0b0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000001_0000000000000000;

    let h: b256 = 0b0000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000_1000000000000000;

    let saturated: b256 =
    0b1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111;

    let highest_bit_only: b256 = 0b1000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000_0000000000000000;

    let all_but_highest_bit: b256 =
    0b1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111_1111111111111111;

    assert(one >> 1 == ZERO);
    assert(one << 1 == two);
    assert(two << 1 == 0x0000000000000000000000000000000000000000000000000000000000000004);
    assert(f << 1 == g);
    assert(c >> 1 == h);
    assert(0x0000000000000000000000000000000000000000000000000000000000000001 << 10 == 0x0000000000000000000000000000000000000000000000000000000000000400);
    assert(0x000000000000000000000000000000000000000000000000000000000AB1142C >> 3 == 0x0000000000000000000000000000000000000000000000000000000001562285);
    assert(saturated << 255 == highest_bit_only);

    ///////////////////////////////////////////////////////
    // test Ord
    ///////////////////////////////////////////////////////

    assert(one > ZERO);
    assert(two > one);
    assert(one < two);
    assert(two < saturated);
    assert(highest_bit_only < saturated);
    assert(saturated > highest_bit_only);
    assert(highest_bit_only > all_but_highest_bit);
    assert(saturated > 0x5555555555555555555555555555555555555555555555555555555555555555);
    assert(0x5555555555555555555555555555555555555555555555555555555555555555 > 0x4444444444444444444444444444444444444444444444444444444444444444);

    // test differences in only one word
    let foo: b256 = 0x0111111111111111_1111111111111111_1111111111111111_1111111111111111;
    let bar: b256 = 0x1111111111111111_0111111111111111_1111111111111111_1111111111111111;
    let baz: b256 = 0x1111111111111111_1111111111111111_0111111111111111_1111111111111111;
    let fiz: b256 = 0x1111111111111111_1111111111111111_1111111111111111_0111111111111111;

    let w: b256 = 0xF000000000000000_E000000000000000_E000000000000000_E000000000000000;
    let x: b256 = 0xE000000000000000_F000000000000000_E000000000000000_E000000000000000;
    let y: b256 = 0xE000000000000000_E000000000000000_F000000000000000_E000000000000000;
    let z: b256 = 0xE000000000000000_E000000000000000_E000000000000000_F000000000000000;

    assert(foo < bar);
    assert(bar < baz);
    assert(baz < fiz);
    assert(fiz > baz);
    assert(baz > bar);
    assert(bar > foo);

    assert(w > x);
    assert(x > y);
    assert(y > z);
    assert(z < y);
    assert(y < x);
    assert(x < w);

    // OrdEq
    assert(x <= w);
    assert(w >= x);
    assert(foo >= foo);
    assert(foo <= foo);
    assert(fiz >= baz);
    assert(foo <= fiz);

    ///////////////////////////////////////////////////////
    // test Add
    ///////////////////////////////////////////////////////

    log_b256(one + two);
    assert(0x0000000000000000_0000000000000000_0000000000000000_0000000000000001 + 0x0000000000000000_0000000000000000_0000000000000000_0000000000000010 == 0x0000000000000000_0000000000000000_0000000000000000_0000000000000011);


    true
}

