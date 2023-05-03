
/// Does not return true for opcode prefix 0x0f
pub fn is_prefix(byte: u8) -> bool {
    let index = byte as usize >> 2;
    let shift = (byte & 3) << 1;
    (INSTRUCTION_INFO[index] >> shift) & 3 == 3
}

/// input 0x100 .. 0x200 = 0f xx
pub fn is_modrm_instruction(opcode: usize) -> bool {
    let index = opcode >> 2;
    let shift = (opcode & 3) << 1;
    (INSTRUCTION_INFO[index] >> shift) & 3 == 1
}

/// 2 bits per instruction:
/// 00 = Nothing
/// 01 = Has modrm byte
/// 10 = Relative u32 jump
/// 11 = Prefix
static INSTRUCTION_INFO: [u8; 0x80] = [
    //            03 02 01 00    07 06 05 04    0b 0a 09 08    0f 0e 0d 0c
    /* 00 */    0b01_01_01_01, 0b00_00_00_00, 0b01_01_01_01, 0b00_00_00_00,
    /* 10 */    0b01_01_01_01, 0b00_00_00_00, 0b01_01_01_01, 0b00_00_00_00,
    /* 20 */    0b01_01_01_01, 0b00_00_00_00, 0b01_01_01_01, 0b00_00_00_00,
    /* 30 */    0b01_01_01_01, 0b00_00_00_00, 0b01_01_01_01, 0b00_00_00_00,
    /* 40 */    0b11_11_11_11, 0b11_11_11_11, 0b11_11_11_11, 0b11_11_11_11,
    /* 50 */    0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* 60 */    0b01_00_00_00, 0b11_11_11_11, 0b01_00_01_00, 0b00_00_00_00,
    /* 70 */    0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* 80 */    0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 90 */    0b00_00_00_00, 0b00_00_00_00, 0b11_00_00_00, 0b00_00_00_00,
    /* a0 */    0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* b0 */    0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* c0 */    0b00_00_01_01, 0b01_01_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* d0 */    0b01_01_01_01, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00,
    /* e0 */    0b00_00_00_00, 0b00_00_00_00, 0b00_00_10_10, 0b00_00_00_00,
    /* f0 */    0b11_11_00_00, 0b01_01_00_00, 0b00_00_00_00, 0b01_01_00_00,
    //            03 02 01 00    07 06 05 04    0b 0a 09 08    0f 0e 0d 0c
    /* 0f 00 */ 0b00_00_00_00, 0b00_00_00_00, 0b00_00_00_00, 0b00_00_01_00,
    /* 0f 10 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 20 */ 0b00_00_00_00, 0b00_00_00_00, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 30 */ 0b00_00_00_00, 0b00_00_00_00, 0b01_01_01_01, 0b00_00_00_00,
    /* 0f 40 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 50 */ 0b01_01_01_00, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 60 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 70 */ 0b00_00_00_01, 0b00_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f 80 */ 0b10_10_10_10, 0b10_10_10_10, 0b10_10_10_10, 0b10_10_10_10,
    /* 0f 90 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f a0 */ 0b01_00_00_00, 0b00_00_01_01, 0b01_00_00_00, 0b01_00_01_01,
    /* 0f b0 */ 0b01_00_01_01, 0b01_01_00_00, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f c0 */ 0b01_01_01_01, 0b01_01_01_01, 0b00_00_00_00, 0b00_00_00_00,
    /* 0f d0 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f e0 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
    /* 0f f0 */ 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01, 0b01_01_01_01,
];