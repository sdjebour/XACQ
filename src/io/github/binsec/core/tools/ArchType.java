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

package io.github.binsec.core.tools;

public enum ArchType {
    X86_64,
    ARM32;
	
	public Integer getPtrSize() {
		switch (this) {
		case X86_64:
			return 64;
		case ARM32:
			return 32;
		default:
			assert false: "unknown ArchType";
			return null;
		}
	}

	public Integer getPtrSizeMemCell() {
		switch (this) {
		case X86_64:
			return 8;
		case ARM32:
			return 8;
		default:
			assert false: "unknown ArchType";
			return null;
		}
	}

}
