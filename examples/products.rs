/*

This program is used to study the combinatorical properties
of normalized expressions of products (select expressions).

*/

use joker_calculus::*;
use num_bigint::BigUint;
use cuckoofilter::CuckooFilter;
use std::collections::hash_map::DefaultHasher;

fn main() {
    let v = vec![platonism(), seshatism()];
    let mut filter: CuckooFilter<DefaultHasher> =
        CuckooFilter::with_capacity(15_000_000_000);

    let l = 4;
    let n: u32 = (2 << l) - 1;
    let mut ind = BigUint::from(0 as u64);
    let mut count = BigUint::from(0 as u64);
    let end = BigUint::from(2 as u32).pow(n);
    let mut it = 0;
    let print_it = 1_000_000;
    while ind < end {
        if it % print_it == 0 {
            println!("{}\n{}\n{}\n\n", ind, end, count.clone() * (2 as u32));
        }
        it %= print_it;
        it += 1;
        let a = constr(&ind, 0, l, &v);
        let b = a.eval_open();
        // println!("{:08b}\n - {:?}\n - {:?}", ind, a, b);
        if !filter.contains(&b) {
            // println!("{:?}", a);
            let _ = filter.add(&b);
            count += 1 as u32;
        }

        ind += 1 as u32;
    }

    println!("{}", count * (2 as u32));
}

fn constr(ind: &BigUint, off: u64, depth: u32, v: &[Expr]) -> Expr {
    if depth == 0 {
        let (i, j) = pair(ind, off);
        sel(v[i].clone(), v[j].clone())
    } else {
        sel(
            constr(ind, off, depth - 1, v),
            constr(ind, off + (1 << depth), depth - 1, v),
        )
    }
}

fn pair(ind: &BigUint, off: u64) -> (usize, usize) {
    (if ind.bit(off) {1} else {0}, if ind.bit(off + 1) {1} else {0})
}
