import KernelCells.Block00
import KernelCells.Block01
import KernelCells.Block02
import KernelCells.Block03
import KernelCells.Block04
import KernelCells.Block05
import KernelCells.Block06
import KernelCells.Block07
import KernelCells.Block08
import KernelCells.Block09
import KernelCells.Block10
import KernelCells.Block11
import KernelCells.Block12
import KernelCells.Block13
import KernelCells.Block14
import KernelCells.Block15
import KernelCells.Block16
import KernelCells.Block17
import KernelCells.Block18
import KernelCells.Block19
import KernelCells.Block20
import KernelCells.Block21
import KernelCells.Block22
import KernelCells.Block23
import KernelCells.Block24
import KernelCells.Block25
import KernelCells.Block26
import KernelCells.Block27
import KernelCells.Block28
import KernelCells.Block29
import KernelCells.Block30
import KernelCells.Block31
import KernelCells.Block32
import KernelCells.Block33
import KernelCells.Block34
import KernelCells.Block35
import KernelCells.Block36
import KernelCells.Block37
import KernelCells.Block38
import KernelCells.Block39
import KernelCells.Block40
import KernelCells.Block41
import KernelCells.Block42
import KernelCells.Block43
import KernelCells.Block44
import KernelCells.Block45
import KernelCells.Block46
import KernelCells.Block47
import KernelCells.Block48
import KernelCells.Block49
import KernelCells.Block50
import KernelCells.Block51
import KernelCells.Block52
import KernelCells.Block53
import KernelCells.Block54
import KernelCells.Block55
import KernelCells.Block56
import KernelCells.Block57
import KernelCells.Block58
import KernelCells.Block59
import KernelCells.Block60
import KernelCells.Block61
import KernelCells.Block62
import KernelCells.Block63
import KernelCells.Block64
import KernelCells.Block65

namespace QuarticKernel

theorem actual_cells_kernel : checkCoreCells = true := by
  apply checkCoreCells_of_ranges
  intro k hk
  interval_cases k
  · exact KernelCells.block0
  · exact KernelCells.block1
  · exact KernelCells.block2
  · exact KernelCells.block3
  · exact KernelCells.block4
  · exact KernelCells.block5
  · exact KernelCells.block6
  · exact KernelCells.block7
  · exact KernelCells.block8
  · exact KernelCells.block9
  · exact KernelCells.block10
  · exact KernelCells.block11
  · exact KernelCells.block12
  · exact KernelCells.block13
  · exact KernelCells.block14
  · exact KernelCells.block15
  · exact KernelCells.block16
  · exact KernelCells.block17
  · exact KernelCells.block18
  · exact KernelCells.block19
  · exact KernelCells.block20
  · exact KernelCells.block21
  · exact KernelCells.block22
  · exact KernelCells.block23
  · exact KernelCells.block24
  · exact KernelCells.block25
  · exact KernelCells.block26
  · exact KernelCells.block27
  · exact KernelCells.block28
  · exact KernelCells.block29
  · exact KernelCells.block30
  · exact KernelCells.block31
  · exact KernelCells.block32
  · exact KernelCells.block33
  · exact KernelCells.block34
  · exact KernelCells.block35
  · exact KernelCells.block36
  · exact KernelCells.block37
  · exact KernelCells.block38
  · exact KernelCells.block39
  · exact KernelCells.block40
  · exact KernelCells.block41
  · exact KernelCells.block42
  · exact KernelCells.block43
  · exact KernelCells.block44
  · exact KernelCells.block45
  · exact KernelCells.block46
  · exact KernelCells.block47
  · exact KernelCells.block48
  · exact KernelCells.block49
  · exact KernelCells.block50
  · exact KernelCells.block51
  · exact KernelCells.block52
  · exact KernelCells.block53
  · exact KernelCells.block54
  · exact KernelCells.block55
  · exact KernelCells.block56
  · exact KernelCells.block57
  · exact KernelCells.block58
  · exact KernelCells.block59
  · exact KernelCells.block60
  · exact KernelCells.block61
  · exact KernelCells.block62
  · exact KernelCells.block63
  · exact KernelCells.block64
  · exact KernelCells.block65

#print axioms actual_cells_kernel

end QuarticKernel
