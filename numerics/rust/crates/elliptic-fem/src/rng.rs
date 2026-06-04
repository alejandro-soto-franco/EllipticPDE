//! A small reproducible PRNG (SplitMix64) for the mesh-perturbation ensemble.
//!
//! The ensemble uses randomly jittered meshes to put error bars on the otherwise
//! deterministic finite-element quantities, so the spread is reproducible from a
//! fixed seed rather than depending on a system RNG.

/// SplitMix64: a fast, well-distributed 64-bit generator with a 64-bit seed.
#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// Seed the generator.
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    /// Next raw 64-bit value.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform on `[0, 1)`.
    pub fn next_f64(&mut self) -> f64 {
        // 53 bits of mantissa precision.
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Uniform on `[-1, 1)`.
    pub fn next_signed(&mut self) -> f64 {
        2.0 * self.next_f64() - 1.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reproducible_from_seed() {
        let mut a = SplitMix64::new(42);
        let mut b = SplitMix64::new(42);
        for _ in 0..100 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn f64_in_unit_interval() {
        let mut r = SplitMix64::new(7);
        for _ in 0..1000 {
            let x = r.next_f64();
            assert!((0.0..1.0).contains(&x));
            let s = r.next_signed();
            assert!((-1.0..1.0).contains(&s));
        }
    }

    #[test]
    fn mean_near_zero_for_signed() {
        let mut r = SplitMix64::new(123);
        let n = 100_000;
        let mean = (0..n).map(|_| r.next_signed()).sum::<f64>() / n as f64;
        assert!(mean.abs() < 0.02, "signed mean {mean}");
    }
}
