use slotmap::Key;

use crate::systems::wccs::wccs_system::WCCSSystem;

struct WCTLSystem<'a, ProcKey: Key> {
    wccs_system: WCCSSystem<'a, ProcKey>,
}
