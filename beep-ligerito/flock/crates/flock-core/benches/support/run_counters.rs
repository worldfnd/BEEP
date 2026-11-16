// [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: what a prover run used, besides its
// wall time, for `benches/ligerito_three_way.rs` (to understand timings that are not what we expect, e.g. a
// prover that is slower in one process than in another). Not part of upstream Flock. Research, unaudited.
// Please review]

//! Resource counters of the process between two points: CPU time, the part
//! of it on performance cores, the time its threads waited for a core,
//! instructions and cycles (and their part on performance cores), energy,
//! page faults and context switches.
//!
//! macOS only: `proc_pid_rusage` with flavor `RUSAGE_INFO_V6`
//! (`<sys/resource.h>`, `struct rusage_info_v6`) and `getrusage`. On another
//! system, or if a call fails, every counter reads zero and `available` is
//! false. A snapshot is two system calls (a few microseconds); the bench
//! takes it outside the region that it times.

use serde_json::{Value, json};

/// The counters at one point in time, as the system reports them.
#[derive(Clone, Copy)]
pub struct Snapshot {
    available: bool,
    /// `rusage_info_v6` after its 16-byte uuid, as 64-bit words.
    info: [u64; 48],
    faults: i64,
    csw_voluntary: i64,
    csw_involuntary: i64,
}

impl Default for Snapshot {
    fn default() -> Self {
        Self {
            available: false,
            info: [0; 48],
            faults: 0,
            csw_voluntary: 0,
            csw_involuntary: 0,
        }
    }
}

// Indices of the fields of `rusage_info_v6` that we read (after the uuid).
const USER_TIME: usize = 0;
const SYSTEM_TIME: usize = 1;
const PKG_IDLE_WKUPS: usize = 2;
const INTERRUPT_WKUPS: usize = 3;
const QOS_FIRST: usize = 18; // default, maintenance, background, utility, legacy, user initiated, user interactive
const INSTRUCTIONS: usize = 29;
const CYCLES: usize = 30;
const RUNNABLE_TIME: usize = 34;
const USER_PTIME: usize = 36;
const SYSTEM_PTIME: usize = 37;
const PINSTRUCTIONS: usize = 38;
const PCYCLES: usize = 39;
const ENERGY_NJ: usize = 40;
const PENERGY_NJ: usize = 41;
const QOS_NAMES: [&str; 7] = [
    "default",
    "maintenance",
    "background",
    "utility",
    "legacy",
    "user_initiated",
    "user_interactive",
];

#[cfg(target_os = "macos")]
mod sys {
    use std::os::raw::{c_int, c_void};

    pub const RUSAGE_INFO_V6: c_int = 6;
    pub const RUSAGE_SELF: c_int = 0;

    #[repr(C)]
    pub struct Timebase {
        pub numer: u32,
        pub denom: u32,
    }

    #[repr(C)]
    #[derive(Default)]
    pub struct Timeval {
        pub sec: i64,
        pub usec: i32,
    }

    /// `struct rusage` of `<sys/resource.h>`.
    #[repr(C)]
    #[derive(Default)]
    pub struct RUsage {
        pub utime: Timeval,
        pub stime: Timeval,
        pub maxrss: i64,
        pub ixrss: i64,
        pub idrss: i64,
        pub isrss: i64,
        pub minflt: i64,
        pub majflt: i64,
        pub nswap: i64,
        pub inblock: i64,
        pub oublock: i64,
        pub msgsnd: i64,
        pub msgrcv: i64,
        pub nsignals: i64,
        pub nvcsw: i64,
        pub nivcsw: i64,
    }

    unsafe extern "C" {
        pub fn proc_pid_rusage(pid: c_int, flavor: c_int, buffer: *mut c_void) -> c_int;
        pub fn getpid() -> c_int;
        pub fn mach_timebase_info(info: *mut Timebase) -> c_int;
        pub fn getrusage(who: c_int, usage: *mut RUsage) -> c_int;
    }
}

/// Nanoseconds per unit of the times of `rusage_info` (Mach absolute time).
#[cfg(target_os = "macos")]
fn tick_ns() -> f64 {
    let mut tb = sys::Timebase { numer: 0, denom: 0 };
    // SAFETY: `mach_timebase_info` writes the two fields of the struct.
    let rc = unsafe { sys::mach_timebase_info(&mut tb) };
    if rc != 0 || tb.denom == 0 {
        return 1.0;
    }
    f64::from(tb.numer) / f64::from(tb.denom)
}

#[cfg(not(target_os = "macos"))]
fn tick_ns() -> f64 {
    1.0
}

impl Snapshot {
    /// The counters of this process now.
    #[cfg(target_os = "macos")]
    pub fn now() -> Self {
        // 16 bytes of uuid and then 64-bit fields; the buffer is larger than
        // any flavor of the struct.
        let mut raw = [0u64; 128];
        let mut ru = sys::RUsage::default();
        // SAFETY: the kernel writes at most `sizeof(struct rusage_info_v6)`
        // (464 bytes) into the 1024-byte buffer, and `getrusage` fills `ru`.
        let (a, b) = unsafe {
            (
                sys::proc_pid_rusage(sys::getpid(), sys::RUSAGE_INFO_V6, raw.as_mut_ptr().cast()),
                sys::getrusage(sys::RUSAGE_SELF, &mut ru),
            )
        };
        if a != 0 || b != 0 {
            return Self::default();
        }
        let mut info = [0u64; 48];
        info.copy_from_slice(&raw[2..50]);
        Self {
            available: true,
            info,
            faults: ru.minflt,
            csw_voluntary: ru.nvcsw,
            csw_involuntary: ru.nivcsw,
        }
    }

    #[cfg(not(target_os = "macos"))]
    pub fn now() -> Self {
        Self::default()
    }

    /// What the process used since `earlier`.
    pub fn since(&self, earlier: &Self) -> Used {
        let ok = self.available && earlier.available;
        let tick_ms = tick_ns() / 1e6;
        let d = |i: usize| self.info[i].wrapping_sub(earlier.info[i]) as f64;
        let mut qos_ms = [0.0; 7];
        for (i, q) in qos_ms.iter_mut().enumerate() {
            *q = d(QOS_FIRST + i) * tick_ms;
        }
        Used {
            available: ok,
            user_ms: d(USER_TIME) * tick_ms,
            system_ms: d(SYSTEM_TIME) * tick_ms,
            user_p_ms: d(USER_PTIME) * tick_ms,
            system_p_ms: d(SYSTEM_PTIME) * tick_ms,
            runnable_ms: d(RUNNABLE_TIME) * tick_ms,
            instructions: d(INSTRUCTIONS),
            cycles: d(CYCLES),
            p_instructions: d(PINSTRUCTIONS),
            p_cycles: d(PCYCLES),
            energy_mj: d(ENERGY_NJ) / 1e6,
            p_energy_mj: d(PENERGY_NJ) / 1e6,
            interrupt_wakeups: d(INTERRUPT_WKUPS),
            idle_wakeups: d(PKG_IDLE_WKUPS),
            faults: (self.faults - earlier.faults) as f64,
            csw_voluntary: (self.csw_voluntary - earlier.csw_voluntary) as f64,
            csw_involuntary: (self.csw_involuntary - earlier.csw_involuntary) as f64,
            qos_ms,
        }
    }
}

/// What the process used between two snapshots.
#[derive(Clone, Copy, Default)]
pub struct Used {
    pub available: bool,
    /// CPU time in user and in system mode, over all threads.
    pub user_ms: f64,
    pub system_ms: f64,
    /// The part of them on performance cores.
    pub user_p_ms: f64,
    pub system_p_ms: f64,
    /// Time that threads were ready to run and had no core.
    pub runnable_ms: f64,
    pub instructions: f64,
    pub cycles: f64,
    /// The part of them on performance cores.
    pub p_instructions: f64,
    pub p_cycles: f64,
    pub energy_mj: f64,
    pub p_energy_mj: f64,
    pub interrupt_wakeups: f64,
    pub idle_wakeups: f64,
    /// Page faults that needed no I/O (`ru_minflt`).
    pub faults: f64,
    pub csw_voluntary: f64,
    pub csw_involuntary: f64,
    /// CPU time by quality-of-service class of the thread.
    pub qos_ms: [f64; 7],
}

fn median(v: &[f64]) -> f64 {
    let mut v = v.to_vec();
    v.sort_by(|a, b| a.partial_cmp(b).expect("no NaN"));
    let n = v.len();
    if n == 0 {
        f64::NAN
    } else if n % 2 == 1 {
        v[n / 2]
    } else {
        0.5 * (v[n / 2 - 1] + v[n / 2])
    }
}

/// The counters of the repetitions of one variant, as JSON: per counter the
/// values of every repetition (`reps`) and their median, and a few derived
/// medians (`wall_ms[i]` is the wall time of repetition `i`).
pub fn to_json(runs: &[Used], wall_ms: &[f64]) -> Value {
    if runs.is_empty() || !runs.iter().all(|u| u.available) {
        return Value::Null;
    }
    let col = |f: &dyn Fn(&Used) -> f64| -> Vec<f64> { runs.iter().map(|u| f(u)).collect() };
    let fields: [(&str, &dyn Fn(&Used) -> f64); 17] = [
        ("user_ms", &|u| u.user_ms),
        ("system_ms", &|u| u.system_ms),
        ("user_p_ms", &|u| u.user_p_ms),
        ("system_p_ms", &|u| u.system_p_ms),
        ("runnable_ms", &|u| u.runnable_ms),
        ("instructions", &|u| u.instructions),
        ("cycles", &|u| u.cycles),
        ("p_instructions", &|u| u.p_instructions),
        ("p_cycles", &|u| u.p_cycles),
        ("energy_mj", &|u| u.energy_mj),
        ("p_energy_mj", &|u| u.p_energy_mj),
        ("interrupt_wakeups", &|u| u.interrupt_wakeups),
        ("idle_wakeups", &|u| u.idle_wakeups),
        ("faults", &|u| u.faults),
        ("csw_voluntary", &|u| u.csw_voluntary),
        ("csw_involuntary", &|u| u.csw_involuntary),
        ("cpu_ms", &|u| u.user_ms + u.system_ms),
    ];
    let mut reps = json!({});
    let mut med = json!({});
    for (name, f) in fields {
        let values = col(f);
        med[name] = json!(median(&values));
        reps[name] = json!(values);
    }
    let mut qos = json!({});
    for (i, name) in QOS_NAMES.iter().enumerate() {
        qos[*name] = json!(median(&col(&|u| u.qos_ms[i])));
    }
    // Derived, per repetition and then the median: threads busy on average,
    // the part of the CPU time on performance cores, cycles per second of
    // CPU time, instructions per cycle.
    let ratio = |num: &dyn Fn(&Used) -> f64, den: &dyn Fn(&Used) -> f64| -> f64 {
        median(&runs.iter().map(|u| num(u) / den(u)).collect::<Vec<_>>())
    };
    let busy: Vec<f64> = runs
        .iter()
        .zip(wall_ms)
        .map(|(u, &w)| (u.user_ms + u.system_ms) / w)
        .collect();
    json!({
        "median": med,
        "reps": reps,
        "qos_ms": qos,
        "threads_busy": median(&busy),
        "p_core_share_of_cpu_time": ratio(&|u| u.user_p_ms + u.system_p_ms, &|u| u.user_ms + u.system_ms),
        "p_core_share_of_instructions": ratio(&|u| u.p_instructions, &|u| u.instructions),
        "ghz": ratio(&|u| u.cycles, &|u| (u.user_ms + u.system_ms) * 1e6),
        "p_ghz": ratio(&|u| u.p_cycles, &|u| (u.user_p_ms + u.system_p_ms) * 1e6),
        "instructions_per_cycle": ratio(&|u| u.instructions, &|u| u.cycles),
        "system_share_of_cpu_time": ratio(&|u| u.system_ms, &|u| u.user_ms + u.system_ms),
    })
}
