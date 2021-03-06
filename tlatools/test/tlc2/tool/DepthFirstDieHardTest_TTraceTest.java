/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class DepthFirstDieHardTest_TTraceTest extends TTraceModelCheckerTestCase {

	public DepthFirstDieHardTest_TTraceTest() {
		super(DepthFirstDieHardTest.class, ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT1));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(7);
		expectedTrace.add("/\\ action = \"nondet\"\n/\\ smallBucket = 0\n/\\ bigBucket = 0\n/\\ water_to_pour = 0");
		expectedTrace.add("/\\ action = \"fill big\"\n/\\ smallBucket = 0\n/\\ bigBucket = 5\n/\\ water_to_pour = 0");
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 3\n/\\ bigBucket = 2\n/\\ water_to_pour = 3");
		expectedTrace.add("/\\ action = \"empty small\"\n/\\ smallBucket = 0\n/\\ bigBucket = 2\n/\\ water_to_pour = 3");
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 2\n/\\ bigBucket = 0\n/\\ water_to_pour = 2");
		
		expectedTrace.add("/\\ action = \"fill big\"\n/\\ smallBucket = 2\n/\\ bigBucket = 5\n/\\ water_to_pour = 2");
		
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 3\n/\\ bigBucket = 4\n/\\ water_to_pour = 1");

        final List<String> expectedActions = new ArrayList<>();
		expectedActions.add("<_init line 29, col 5 to line 32, col 48 of module " + getModuleName() + ">");
		expectedActions.addAll(Collections.nCopies(expectedTrace.size() - 1,
				"<_next line 36, col 5 to line 46, col 53 of module " + getModuleName() + ">"));
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		assertZeroUncovered();
	}
}
