type Signed = i32;

pub fn signed_min() -> i64 {
    comptime { -9223372036854775807_i64 - 1_i64 }
}

pub fn signed_alias() -> Signed {
    comptime { -7_i32 }
}

pub fn unsigned_max() -> u128 {
    340282366920938463463374607431768211455
}

pub fn signed_generic() -> i32 {
    identity::<-7_i32>()
}

fn identity<let N: i32>() -> i32 {
    N
}

pub fn byte_string() -> str<3> {
    comptime { [65_u8, 255_u8, 66_u8].as_str_unchecked() }
}

pub fn unicode_string() -> str<2> {
    "é"
}

pub fn escaped_string() -> str<3> {
    "\"\\\n"
}

pub fn field_negative() -> Field {
    comptime { -1 }
}
