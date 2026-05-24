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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.IntVar;

import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.tools.ArchType;

public class ACQ_CellVariable {
	static int nextvarid = 0; // next id for new variables
	static int numberptrcells = 0;
	static int numberintcells = 0; // invariant nextrefaddress <= numberptrcells + numberintcells
	static int numberrefs = 0;
	static int nextptrcellid = 0;
	static int strcontentsize = 0; // store the size required for the pointer type
	static public ArchType arch;

	public int cellid; // the cell id (independently from global or not) printed in smtlib
	int ptrcellid; // the cell id when taking into account only pointer cells (invariant:
					// globalcellid <= cellid)
	boolean global;
	ACQ_RefVariable ref = null;
	ACQ_ValueVariable vv;
	ACQ_ValueVariable size = null;
	private static int maxcoeff = 1;

	static HashSet<Integer> addintconstants = new HashSet<>();
	static HashSet<Integer> adduintconstants = new HashSet<>();
	static boolean bigString = false;

	static HashMap<CellType, Domain> values_domains;
	static ArrayList<Bitvec> addr_globals = new ArrayList<Bitvec>();

	private static Integer getMax(Integer[] l) {
		Integer res = null;
		for (Integer i : l) {
			if (res == null) res = i;
			else if (i != null && res < i) {
				res = i;
			}
		}
		return res;
	}
	
	static public void fixDomains(Integer[] ptr_sizes) {
		/*
		 * Pointers points to different areas depending on their types
		 */
		assert values_domains == null : "Domains already set";
		values_domains = new HashMap<>();
		
		Integer max_ptr_sizes = getMax(ptr_sizes);
		
		int str_max = numberptrcells*2;
		
		int ptr_coef = max_ptr_sizes != null ? max_ptr_sizes : 1;
		int ptr_offset = Integer.max(1000, str_max + getSizeUpper() + 1);
		int ptr_max = numberptrcells*2;
		
		for (CellType t : CellType.values()) {
			switch (t) {
			case PTR: {
				Domain dom = new Domain(t, arch);
				
				dom.add_value(0);
				
				for (int i = 0; i <= ptr_max; i++) {
					dom.add_value(ptr_offset + (ptr_coef * i));
				}
				
				for (Bitvec addr : addr_globals)
					dom.add_value(addr.unsigned().intValue());

				values_domains.put(t, dom);
				break;
			}

			case STR: {
				Domain dom = new Domain(t, arch);
				dom.update_lower(0);
				dom.update_upper(str_max);
				values_domains.put(t, dom);

				break;
			}

			case INT:
			case INT8:{
				int min = addintconstants.size() == 0 ? 0 : Collections.min(addintconstants);
				int max = addintconstants.size() == 0 ? 0 : Collections.max(addintconstants);
				int lower = Math.min(min, -(numberintcells + 1) * maxcoeff);
				int upper = Math.max(max, (numberintcells + 1) * maxcoeff);
				Domain dom = new Domain(t, arch);
				dom.update_lower(lower);
				dom.update_upper(upper);
				values_domains.put(t, dom);
				break;
			}

			case UINT:
			case UINT16:
			case UINT8: {
				int max = adduintconstants.size() == 0 ? 0 : Collections.max(adduintconstants);
				int upper = Math.max(max, numberintcells + 1);
				Domain dom = new Domain(t, arch);
				dom.update_upper(upper);
				values_domains.put(t, dom);
				break;
			}

			case BOOL:
				Domain dom = new Domain(t, arch);
				dom.update_upper(1);
				values_domains.put(t, dom);
				break;
			}
		}
	}

	public int getStrContentSize() {
		return strcontentsize;
	}

	public void setStrContentSize(int n) {
		strcontentsize = n;
	}

	public void setmaxcoeff(int n) {
		maxcoeff = n;
	}

	public static int getSizeUpper() {
		int n = (strcontentsize + 1) * (numberptrcells) * 2;
		return n + n % 4;
	}

	public int getvaluelower() {
		if (getType() == CellType.INT || getType() == CellType.INT8) {
			int min = addintconstants.size() == 0 ? 0 : Collections.min(addintconstants);
			int lower = Math.min(min, -(numberintcells + 1) * maxcoeff);
			return lower;

		} else
			return 0;
	}

	public ACQ_CellVariable(CellType vtype, boolean global, Bitvec refaddr, ArchType arch) {
		this.cellid = getNbCells();

		this.arch = arch;
		this.global = global;

		if (global) {
			// If not global (i.e. parameter), then we have no constraint over the reference
			// to the parameter
			this.ref = new ACQ_RefVariable(nextvarid, refaddr, arch);
			addr_globals.add(refaddr);
			nextvarid++;
			numberrefs++;
		}

		this.vv = new ACQ_ValueVariable(nextvarid, vtype);
		nextvarid++;

		// Depending on the type of the cell, increase the appropriate upper bound
		if (vtype == CellType.STR) {
			// Add variable to represent the size of the pointed data structure
			this.size = new ACQ_ValueVariable(nextvarid, CellType.UINT);
			nextvarid++;

			ptrcellid = nextptrcellid;
			nextptrcellid++;
			numberptrcells++;
		} else if (vtype == CellType.PTR) {
			ptrcellid = nextptrcellid;
			nextptrcellid++;
			numberptrcells++;
		} else if (vtype == CellType.INT || vtype == CellType.INT8 ||vtype == CellType.UINT || vtype == CellType.UINT8
				|| vtype == CellType.UINT16 || vtype == CellType.BOOL)
			numberintcells++;
		else
			assert false : "Unknown type here1";

	}

	public String getRefBwDomain() {
		int addrsize = ACQ_CellVariable.arch.getPtrSize() / 4;
		return String.format("(= v%d #x%0" + addrsize + "x)", getRef().id, getRef().addr.unsigned().intValue());
	}

	public String getValueBwDomain() {
		Domain dom = values_domains.get(getType());
		String varname = String.format("v%d", getValue().id);
		return dom.getBwDomain(varname);
	}

	public String getSizeBwDomain() {
		int n = getSizeUpper();
		return String.format("(bvule v%d #x%04x)\n", getSize().id, n);
	}

	public int getNbCells() {
		return numberptrcells + numberintcells;
	}

	public boolean isGlobal() {
		assert this.global == (this.ref != null);
		return this.global;
	}

	public ACQ_RefVariable getRef() {
		return this.ref;
	}

	public ACQ_ValueVariable getValue() {
		return this.vv;
	}

	public ACQ_ValueVariable getSize() {
		return this.size;
	}

	public IntVar getChocoRef(Model model) {
		// Deprecated
		assert false : "Choco Solver handling is deprecated";
		return null;
	}

	public IntVar getChocoValue(Model model) {
		// Deprecated
		assert false : "Choco Solver handling is deprecated";
		return null;
	}

	public void addValue(int i) {
		if ((getType() == CellType.INT)||getType() == CellType.INT8 ) {
			ACQ_CellVariable.addintconstants.add(i);
		} else if (getType() == CellType.UINT || getType() == CellType.UINT8 || getType() == CellType.UINT16
				|| getType() == CellType.BOOL) {
			if (i >= 0)
				ACQ_CellVariable.adduintconstants.add(i);
		} else
			assert false;
	}

	public IntVar getChocoSize(Model model) {
		// Deprecated
		assert false : "Choco Solver handling is deprecated";
		return null;
	}

	public void setBigString() {
		ACQ_CellVariable.bigString = true;
	}

	public CellType getType() {
		return this.vv.getType();
	}

	public Integer[] rand() {
		Integer res[] = new Integer[3];
		if (this.ref == null) {
			res[0] = null;
		} else {
			res[0] = this.ref.rand();
		}

		res[1] = values_domains.get(getType()).rand();

		// add size (if ptr = NULL, then size equals 1)
		if (getType() != CellType.STR)
			res[2] = null;
		else {
			if (res[1] == 0) {
				res[2] = 1;
			} else {
				res[2] = this.size.rand(1, getSizeUpper());
			}
		}
		return res;
	}

	public String toString() {
		String ref = (this.ref != null) ? "&var" + this.cellid : "_";
		return "(" + ref + " -> " + "var" + this.cellid + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ref == null) ? 0 : ref.hashCode());
		result = prime * result + ((vv == null) ? 0 : vv.hashCode());

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
		ACQ_CellVariable other = (ACQ_CellVariable) obj;

		if (this.isGlobal() != other.isGlobal()) {
			return false;
		}

		if (this.isGlobal()) {
			if (!this.ref.equals(other.ref)) {
				return false;
			}
		}

		if (!this.vv.equals(other.vv)) {
			return false;
		}

		return true;
	}

	public static int[] cellToIntList(ACQ_CellVariable[] cellList) {
		int[] res = new int[cellList.length];
		for (int i = 0; i < cellList.length; i++) {
			res[i] = cellList[i].cellid;
		}
		return res;
	}
}
