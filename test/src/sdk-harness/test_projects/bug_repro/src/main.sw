script;

 fn pow(a: u64, b: u64) -> u64 {
        asm(r1: a, r2: b, r3) {
            exp r3 r1 r2;
            r3: u64
        }
    }

fn main() -> bool {
    pow(100, 100) == 0
}
