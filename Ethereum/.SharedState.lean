import Ethereum.State
import Ethereum.MachineState

namespace Ethereum

structure SharedState extends Ethereum.State, Ethereum.MachineState
  deriving Inhabited

end Ethereum
