/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Ian Morris Nieves - initial design and implementation
 ******************************************************************************/

package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class FingerprintExceptionNextTest extends ModelCheckerTestCase {

	public FingerprintExceptionNextTest() {
		super("FingerprintExceptionNext", ExitStatus.FAILURE_SPEC_EVAL);
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished with a general exception, a fingerprint exception and underlying overflow exception
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.GENERAL));
		String arg1 = "1) line 8, col 51 to line 8, col 63 of module FingerprintExceptionNext\n"
			+ "0) line 8, col 44 to line 8, col 64 of module FingerprintExceptionNext\n";
		String arg2 = "Overflow when computing the number of elements in:\n"
			+ "SUBSET (1..32)";
		assertTrue(recorder.recordedWithStringValues(EC.TLC_FINGERPRINT_EXCEPTION, arg1, arg2));
		
		assertUncovered("line 8, col 71 to line 8, col 76 of module FingerprintExceptionNext: 0\n");
	}
}
