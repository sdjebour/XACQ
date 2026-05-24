/****************************************************************************/
/*  This file is part of PRECA.                                             */
/*  PRECA is part of the BINSEC toolbox for binary-level program analysis.  */
/*                                                                          */
/*  Copyright (C) 2019-2023                                                 */
/*    CEA (Commissariat à l'énergie atomique et aux énergies                */
/*         alternatives)                                                    */
/*                                                                          */
/*  you can redistribute it and/or modify it under the terms of the GNU     */
/*  Lesser General Public License as published by the Free Software         */
/*  Foundation, version 2.1.                                                */
/*                                                                          */
/*  It is distributed in the hope that it will be useful,                   */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of          */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           */
/*  GNU Lesser General Public License for more details.                     */
/*                                                                          */
/*  See the GNU Lesser General Public License version 2.1                   */
/*  for more details (enclosed in the file licenses/LGPLv2.1).              */
/*                                                                          */
/****************************************************************************/

package io.github.binsec.core.acqvariable;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.IntVar;

import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.tools.ArchType;

public class ACQ_RefVariable extends ACQ_Variable {
	public int id;
	public Bitvec addr;
	ArchType arch;

	CellType type = CellType.PTR;

	public ACQ_RefVariable(int id, Bitvec address, ArchType arch) {
		this.id = id;
		this.addr = address;
		this.arch = arch;
	}

	@Override
	public IntVar getChocoVar(Model model, int lower, int upper) {
		return model.intVar(this.getName(), lower, upper);
	}

	@Override
	public IntVar getChocoVar(Model model) {
		int value = addr.unsigned().intValue();
		return model.intVar(this.getName(), value, value);
	}

	@Override
	public CellType getType() {
		return this.type;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + this.id;
		// result = prime * result + this.address;
		result = prime * result + this.type.hashCode();

		return result;
	}

	@Override
	public boolean equals(Object obj) {

		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ACQ_RefVariable other = (ACQ_RefVariable) obj;

		if (this.id != other.id) {
			return false;
		}

		/*
		 * if (this.address != other.address) { return false; }
		 */

		if (this.type != other.type) {
			return false;
		}

		return true;
	}
	
	@Override
	public String getName() {
		return "&var" + this.id;
	}

	public int rand() {
		return addr.unsigned().intValue();
	}
}
