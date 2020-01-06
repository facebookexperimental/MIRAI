#[macro_use]
extern crate mirai_annotations;

fn write_u32_as_uleb128(binary: &mut Vec<u8>, value: u8) {
    binary.push(value);

    binary.push(value);
}

pub fn main() {
    let mut buf = Vec::<u8>::new();
    write_u32_as_uleb128(&mut buf, 129);
    verify!(buf.len() == 2);
}
