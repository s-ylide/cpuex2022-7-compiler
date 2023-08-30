use std::ops::Range;

#[inline]
pub const fn bit_range(r: Range<u32>) -> u32 {
    let large: u32 = if r.end != 31 { 1 << (r.end + 1) } else { 0 };
    large.wrapping_sub(1 << r.start)
}

#[inline]
pub const fn bit_range_lower(index: u32) -> u32 {
    let large: u32 = if index != 31 { 1 << (index + 1) } else { 0 };
    large.wrapping_sub(1)
}

#[inline]
pub const fn mask(bin: u32, r: Range<u32>) -> u32 {
    bin & bit_range(r)
}

#[inline]
pub const fn mask_lower(bin: u32, index: u32) -> u32 {
    bin & bit_range_lower(index)
}

#[inline]
pub const fn extract(bin: u32, r: Range<u32>) -> u32 {
    let left = r.start;
    mask(bin, r) >> left
}

#[inline]
pub const fn at(bin: u32, index: u32) -> u32 {
    (bin >> index) & 1
}

#[inline]
pub const fn within(bin: u32, width: u32) -> bool {
    bin < (1 << width)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_range_lower() {
        assert_eq!(bit_range_lower(19), 0xfffff)
    }
}
