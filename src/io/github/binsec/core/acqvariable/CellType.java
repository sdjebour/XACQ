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

import io.github.binsec.core.tools.ArchType;

public enum CellType {
	PTR,
	STR,
	INT,
	INT8,
	UINT,
	UINT8,
	UINT16,
	BOOL;
	
	public int getSize(ArchType t) {
		switch (this) {
		case PTR:
		case STR:
			return t.getPtrSize();
		case INT:
		case UINT:
			return 32;
		case UINT8:
		case INT8:
			return 8;
		case UINT16:
			return 16;
		case BOOL:
			return 8;
		}
		assert false: "unknown CellType";
		return -1;
	}

	public int getSizeMemCell(ArchType arch) {
		switch (this) {
		case PTR:
		case STR:
			return arch.getPtrSizeMemCell();
		default:
			assert false: "unknown CellType or not supported";
			return -1;
		}
	}
	
	public int getNbAcqVars(Boolean global) {
		int res = global ? 1 : 0;
		switch (this) {
		case STR:
			res += 2;
			break;
		default:
			res += 1;
			break;
		}
		return res;
	}
	
	public Boolean isPtrKind() {
		switch (this) {
		case PTR:
		case STR:
			return true;
		default:
			return false;
		}
	}
	
	public Boolean isIntKind() {
		switch (this) {
		case INT:
		case INT8:
		case UINT:
		case UINT8:
		case UINT16:
			return true;
		default:
			return false;
		}
	}
	
	public Boolean isUnsigned() {
		switch (this) {
		case PTR:
		case STR:
		case UINT:
		case UINT8:
		case UINT16:
			return true;
		default:
			return false;
		}
	}
}
