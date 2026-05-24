package io.github.binsec.core.acqvariable;

import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.tools.ArchType;

public class CellWithSizeVariable extends ACQ_CellVariable {


	public CellWithSizeVariable(CellType vtype, boolean global, Bitvec refaddr, ArchType arch) {
		super(vtype, global, refaddr, arch);
		
		if (vtype == CellType.PTR) { 
			nextvarid++;
		}
	}
	
	public int getNbSubVars() {
		int res = isGlobal() ? 1 : 0;
		if (getType() == CellType.PTR) return res + 3;
		else return res + 1;
	}
	

	
	@Override
	public Integer[] rand() {
		Integer tmp[] = super.rand();
		Integer res[] = new Integer[tmp.length+1];
		for (int i = 0; i<tmp.length; i++) res[i] = tmp[i];
		
		if (getType() != CellType.PTR)
			res[3] = null;
		else {
			if (res[1] == 0) {
				res[3] = 0;
			}
			else {
				assert false : "is this really called ?";
				int upper = numberptrcells + 1;
				res[3] = this.size.rand(1, upper);
			}
		}
		return res;
	}
}
