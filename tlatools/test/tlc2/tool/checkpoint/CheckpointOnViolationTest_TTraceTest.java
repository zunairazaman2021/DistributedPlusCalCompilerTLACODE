/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.tool.checkpoint;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class CheckpointOnViolationTest_TTraceTest extends TTraceModelCheckerTestCase {

	public CheckpointOnViolationTest_TTraceTest() {
		super(CheckpointOnViolationTest.class, ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states. 
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "7", "7", "0"));
		
		// Check the violation
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		assertEquals(7, recorder.getRecords(EC.TLC_STATE_PRINT2).size());
		
		assertZeroUncovered();
	}

	@Override
	protected int doCheckpoint() {
		// Request checkpoints but make it highly unlike for the test to ever create a
		// checkpoint because the checkpoint interval was exceeded. We want to test
		// TLC's functionality to take a checkpoint when time-bound model-checking is on
		// and/or a violation has been found.
		return (Integer.MAX_VALUE / 60000);
	}
}
