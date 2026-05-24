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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.zaxxer.nuprocess.NuAbstractProcessHandler;
import com.zaxxer.nuprocess.NuProcess;
import com.zaxxer.nuprocess.NuProcessBuilder;

import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.acqvariable.CellType;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.Explanation;

public class Binsec {

	String binpath;
	String binsec_init;
	Integer emultimeout = 60;
	CellType[] types;
	boolean[] globals;
	Bitvec[] addrs_global;
	int last_offset = 0;
	ArchType arch;
	int arch_size = 0;
	ACQ_CellVariable[] cells;

	String[] binsec_command(File temp) {
		if (arch == ArchType.ARM32) {
			return new String[] { "binsec", "-sse", "-sse-engine", "exepath", "-sse-script", temp.getPath(), binpath,
					"-emul-perm",
					String.format("%s/resources/permissions%02d.config", System.getenv("PRECA_PATH"), arch_size),
					"-sse-timeout", emultimeout.toString(), "-sse-no-screen", "-arm-supported-modes", "thumb" };
		} else if (arch == ArchType.X86_64) {
			return new String[] { "binsec", "-sse", "-sse-engine", "exepath", "-sse-script", temp.getPath(), binpath,
					"-emul-perm",
					String.format("%s/resources/permissions%02d.config", System.getenv("PRECA_PATH"), arch_size),
					"-sse-timeout", emultimeout.toString(), "-sse-no-screen" };
		}
		assert false : "Architecture not supported";
		return null;

	}

	int id = 1;

	Runtime runtime;

	void set_arch_size(ArchType arch) {
		switch (arch) {
		case ARM32:
			this.arch_size = 32;
			break;
		case X86_64:
			this.arch_size = 64;
			break;
		default:
			assert false;
		}

	}

	public Binsec(String conffile, CellType[] types, boolean[] globals, ArchType arch) {

		this.types = types;
		this.globals = globals;
		this.runtime = Runtime.getRuntime();
		this.arch = arch;
		set_arch_size(arch);

		try (BufferedReader br = Files.newBufferedReader(Paths.get(conffile))) {
			// read line by line
			String line;
			while ((line = br.readLine()) != null) {
				if (line.startsWith("bin:")) {
					binpath = line.split(":")[1].strip();
				} else if (line.startsWith("emultimeout:")) {
					emultimeout = Integer.parseInt(line.split(":")[1].strip());
				} else if (line.startsWith("addr_globals:")) {
					String[] saddrs = line.split(":")[1].strip().split(",");
					addrs_global = new Bitvec[saddrs.length];
					for (int i = 0; i < saddrs.length; i++) {
						String hex_no_0x = saddrs[i].split("x")[1];
						addrs_global[i] = new Bitvec(new BigInteger(hex_no_0x, 16), 32);

					}
				} else if (line.startsWith("binsec:")) {
					Path filePath = Path.of(line.split(":")[1].strip());
					binsec_init = Files.readString(filePath);
				}
			}

		} catch (IOException e) {
			System.err.format("IOException: %s%n", e);
		}
	}

	public void setCells(ACQ_CellVariable[] cells) {
		this.cells = cells;
	}

	private String get_dba_cmd(int cell_index, BigInteger value, Bitvec size, Bitvec ref, CellType type) {
		String dba_cmd = "";

		if (type.isPtrKind()) dba_cmd += String.format("x%d<%d> := nondet_ptr as x%d\n", cells[cell_index].cellid, type.getSize(arch), cells[cell_index].cellid);
		else dba_cmd += String.format("x%d<%d> := nondet\n", cells[cell_index].cellid, type.getSize(arch));
		dba_cmd += String.format("assume x%d= %s\n", cells[cell_index].cellid, value);

		if (type == CellType.STR) {
			for (int offset = 0; size.ucompareTo(new Bitvec(BigInteger.valueOf(offset), size.size)) == 1; offset++) {
				dba_cmd += String.format("x%d_%d<%d> := nondet\n", cells[cell_index].cellid, offset,
						CellType.STR.getSizeMemCell(arch));
				dba_cmd += String.format("assume x%d_%d = 0x%02x\n", cells[cell_index].cellid, offset, 41 & 0xff); // TODO
																													// random
																													// byte
																													// non
																													// null
				dba_cmd += String.format("@[x%d+%d,1] := x%d_%d\n", cells[cell_index].cellid, offset,
						cells[cell_index].cellid, offset);
			}
			// System.out.println(value.intValue());
			// if(value.intValue()!=0) {
			dba_cmd += String.format("x%d_%d<%d> := nondet\n", cells[cell_index].cellid, size.unsigned(),
					CellType.STR.getSizeMemCell(arch));
			dba_cmd += String.format("assume x%d_%d = 0x00\n", cells[cell_index].cellid, size.unsigned());
			dba_cmd += String.format("@[x%d+%d,1] := x%d_%d\n", cells[cell_index].cellid, size.unsigned(),
					cells[cell_index].cellid, size.unsigned());

			// }
		}
		return dba_cmd;
	}

	// return the right register depending on the architecture choosen
//	private String calling_convention(int cell_index) {
//		if (arch == ArchType.X86_64) {
//			return calling_convention_x86_64(cell_index);
//		}
//		if (arch == ArchType.ARM32) {
//			return calling_convention_arm32(cell_index);
//
//		}
//		assert false : "not supported architecture";
//		return null;
//	}

	// initialiase registers for binsec
	private String setinputs(String input_template, Bitvec[] inputs) {
		int input_index = 0;
		int cell_index = 0;
		int global_index = 0;

		String prefix = "";
		String template = input_template;
		while (input_index < inputs.length) {

			Bitvec ref = null;
			Bitvec value = null;
			Bitvec size = null;

			if (globals[cell_index]) {
				ref = addrs_global[global_index];
				global_index++;
				input_index++;
			}

			String template_var = null;
			String xvar = null;

			CellType celltype = types[cell_index];

			switch (celltype) {

			case STR:
				value = inputs[input_index];
				input_index++;

				size = inputs[input_index];
				input_index++;

				prefix += get_dba_cmd(cell_index, value.unsigned(), size, ref, celltype);
				template_var = String.format("{v%d}", cells[cell_index].cellid);
				xvar = String.format("x%d", cells[cell_index].cellid);
				template = template.replace(template_var, xvar);
				break;

			
			case INT:
			case INT8:
				value = inputs[input_index];
				input_index++;

				prefix += get_dba_cmd(cell_index, value.signed(), size, ref, celltype);
				template_var = String.format("{v%d}", cells[cell_index].cellid);
				xvar = String.format("x%d", cells[cell_index].cellid);
				template = template.replace(template_var, xvar);
				break;
			case PTR:
			case UINT:
			case UINT8:
			case UINT16:
			case BOOL:
				value = inputs[input_index];
				input_index++;

				prefix += get_dba_cmd(cell_index, value.unsigned(), size, ref, celltype);
				template_var = String.format("{v%d}", cells[cell_index].cellid);
				xvar = String.format("x%d", cells[cell_index].cellid);
				template = template.replace(template_var, xvar);
				break;

			default:
				assert false;
			}
			cell_index++;
		}
		return prefix + "\n" + template + "\nstart_exe";

	}

	private String getInitPrefix() {
		String[] lines = binsec_init.split("\n");
		String res = "";
		for (String line : lines) {
			// Stops at first line with template {v%d}
			if (line.contains("{v")) {
				break;
			} else {
				res += line + "\n";
			}
		}
		return res;
	}

	private String getInputTemplate() {
		String[] lines = binsec_init.split("\n");
		String res = "";
		Boolean store = false;
		for (String line : lines) {
			// Start at first line with template {v%d}
			store = store || line.contains("{v");

			if (store) {
				res += line + "\n";
			}
		}
		return res;
	}

	public int call(Bitvec[] inputs) {
		// System.out.println(Arrays.toString(inputs));
		String binsec_init_prefix = getInitPrefix();
		String input_template = getInputTemplate();
		String config = binsec_init_prefix + "\n\n" + setinputs(input_template, inputs);
//		System.out.println(config);

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("binsec_config_", ".txt");
			myWriter = new FileWriter(temp);
			myWriter.write(config);
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		// Process proc;
		int res = 0;

		CompletableFuture<Integer> exitFuture = new CompletableFuture<>();
		// System.out.println(Arrays.deepToString(binsec_command(temp)));
		NuProcessBuilder builder = new NuProcessBuilder(binsec_command(temp));
		StringBuilder stdoutBuilder = new StringBuilder();
		StringBuilder stderrBuilder = new StringBuilder();

		builder.setProcessListener(new NuAbstractProcessHandler() {

			@Override
			public void onStdout(ByteBuffer buffer, boolean closed) {
				if (buffer == null)
					return;
				byte[] bytes = new byte[buffer.remaining()];
				buffer.get(bytes);
				// System.out.print(new String(bytes, StandardCharsets.UTF_8));
				stdoutBuilder.append(new String(bytes, StandardCharsets.UTF_8));
			}

			@Override
			public void onStderr(ByteBuffer buffer, boolean closed) {
				if (buffer == null)
					return;
				byte[] bytes = new byte[buffer.remaining()];
				buffer.get(bytes);
				// System.err.print(new String(bytes, StandardCharsets.UTF_8));
				stderrBuilder.append(new String(bytes, StandardCharsets.UTF_8));
			}

			@Override
			public void onExit(int exitCode) {
				exitFuture.complete(exitCode);
			}
		});

		try {// to complete
			long begin = System.currentTimeMillis();
			NuProcess process = builder.start();
			try {
				int exitCode = exitFuture.get();
				if (exitCode != 0) {
					assert false : "binsec error" + stderrBuilder.toString();
				}
			} catch (ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} // waits asynchronously
				// Start time

			/*
			 * if (proc.exitValue() != 0) { Files.deleteIfExists(temp.toPath()); assert
			 * false : "Error while running Binsec"; }
			 */

			// Access results
			String stdout = stdoutBuilder.toString();
			String stderr = stderrBuilder.toString();

			assert stderr.length() == 0 : "Error in Binsec output : " + stderr;

			// Pattern pattern = Pattern.compile("Formula(?:\\s*@
			// 0x[0-9A-Fa-f]{8})?(.*?)(\\[sse:info\\]|$)", Pattern.DOTALL);
			// Pattern pattern =
			// Pattern.compile("(?s)(?!.*anonymous)(?<=\\[sse:debug\\]\\s*0x[0-9A-Fa-f]+\\s*)[^\\[]*(?=(\\[sse:result\\]|$))");

			/*
			 * while ((s = stdout.readLine()) != null) { //save proc result assert
			 * !s.contains("Cut path") : "Cut path !!!!!!!!!!!!!!!!!";
			 * outputBuffer.append(s).append("\n"); } String output =
			 * outputBuffer.toString();
			 * System.out.println("lengh de l'output"+output.length());
			 */
			if (stdout.contains("[EMUL ERROR]")) {
				res = 1;
			}

			if (System.currentTimeMillis() - begin > emultimeout * 1000)
				res = 1;

			// System.out.println(s);

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		return res;
	}

	public int call(Bitvec[] inputs, Explanation exp, ACQ_Query q) {
		String binsec_init_prefix = getInitPrefix();
		String input_template = getInputTemplate();
		String config = binsec_init_prefix + "\n\n" + setinputs(input_template, inputs);
		//System.out.println("\nfichier config: \n" + config);

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("binsec_config_", ".txt");
			myWriter = new FileWriter(temp);
			myWriter.write(config);
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";
		CompletableFuture<Integer> exitFuture = new CompletableFuture<>();
		String[] s = binsec_command(temp);
		NuProcessBuilder builder = new NuProcessBuilder(binsec_command(temp));
		StringBuilder stdoutBuilder = new StringBuilder();
		StringBuilder stderrBuilder = new StringBuilder();

		builder.setProcessListener(new NuAbstractProcessHandler() {

			@Override
			public void onStdout(ByteBuffer buffer, boolean closed) {
				if (buffer == null)
					return;
				byte[] bytes = new byte[buffer.remaining()];
				buffer.get(bytes);
				// System.out.print(new String(bytes, StandardCharsets.UTF_8));
				stdoutBuilder.append(new String(bytes, StandardCharsets.UTF_8));
			}

			@Override
			public void onStderr(ByteBuffer buffer, boolean closed) {
				if (buffer == null)
					return;
				byte[] bytes = new byte[buffer.remaining()];
				buffer.get(bytes);

				stderrBuilder.append(new String(bytes, StandardCharsets.UTF_8));
			}

			@Override
			public void onExit(int exitCode) {
				exitFuture.complete(exitCode);
			}
		});
		int res = 0;
		try {// to complete
			long begin = System.currentTimeMillis();
			NuProcess process = builder.start();
			try {
				int exitCode = exitFuture.get();
				if (exitCode != 0) {
					assert false : "binsec error" + stderrBuilder.toString();
				}
			} catch (ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} // waits asynchronously
				// Start time

			String stdout = stdoutBuilder.toString();
			String stderr = stderrBuilder.toString();

			assert stderr.length() == 0 : "Error in Binsec output\n" + stderr.toString();

			exp.getFormulaBinsecOutput(stdout, cells, q);
			// System.out.println(exp.getExp());
			exp.setRegId(extractRegId(exp));

			if (stdout.contains("[EMUL ERROR]")) {
				res = 1;
			}

			// Pattern pattern = Pattern.compile("Formula(?:\\s*@
			// 0x[0-9A-Fa-f]{8})?(.*?)(\\[sse:info\\]|$)", Pattern.DOTALL);
			// Pattern pattern =
			// Pattern.compile("(?s)(?!.*anonymous)(?<=\\[sse:debug\\]\\s*0x[0-9A-Fa-f]+\\s*)[^\\[]*(?=(\\[sse:result\\]|$))");

			/*
			 * while ((s = stdInput.readLine()) != null) { //save proc result assert
			 * !s.contains("Cut path") : "Cut path !!!!!!!!!!!!!!!!!";
			 * outputBuffer.append(s).append("\n"); }
			 */

			if (System.currentTimeMillis() - begin > emultimeout * 1000)
				res = 124;
			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		return res;
	}

	public Map<String, String> extractRegId(Explanation exp) {
		Map<String, String> res = new HashMap<>();
		Pattern p = Pattern.compile("\\(declare-fun " + "(x\\d+(?:_\\d+)?)" + // x<i> or x<i>_<j>
				"(?:!([a-zA-Z0-9]+))? " + // optional !id
				"\\(\\) \\(_ BitVec \\d+\\)\\)" // any BitVec size
		);

		try (BufferedReader reader = new BufferedReader(new StringReader(exp.getExp()))) {

			String line;
			while ((line = reader.readLine()) != null) {
				Matcher m = p.matcher(line);
				if (m.matches()) {
					String key = m.group(1); // x<i> or x<i>_<j>
					String value = m.group(2) != null ? m.group(2) : "";

					res.put(key, value);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		return res;
	}

}
