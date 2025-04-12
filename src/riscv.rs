use num_derive::FromPrimitive;

#[derive(Clone, Copy, Debug, FromPrimitive)]
pub enum Trap {
    InstructionAddressMisaligned = 0,
    InstructionAccessFault,
    IllegalInstruction,
    Breakpoint,
    LoadAddressMisaligned,
    LoadAccessFault,
    StoreAddressMisaligned,
    StoreAccessFault,
    EnvironmentCallFromUMode,
    EnvironmentCallFromSMode,
    // Reserved
    EnvironmentCallFromMMode = 11,
    InstructionPageFault,
    LoadPageFault,
    // Reserved
    StorePageFault = 15,

    UserSoftwareInterrupt = 100,
    SupervisorSoftwareInterrupt = 101,
    MachineSoftwareInterrupt = 103,

    UserTimerInterrupt = 104,
    SupervisorTimerInterrupt = 105,
    MachineTimerInterrupt = 107,

    UserExternalInterrupt = 108,
    SupervisorExternalInterrupt = 109,
    MachineExternalInterrupt = 111,
}

#[derive(Clone, Copy, Debug, FromPrimitive, PartialEq, Eq)]
pub enum PrivMode {
    U,
    S,
    Reserved,
    M,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum MemoryAccessType {
    Execute,
    Read,
    Write,
}
