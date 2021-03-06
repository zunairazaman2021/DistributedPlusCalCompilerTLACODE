package tlc2;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import tlc2.output.AbstractSpecWriter;
import tlc2.output.SpecWriterUtilities;
import util.TLAConstants;

/**
 * The class name is quite wordy - but the 'more appropriate' TraceExpressionSpecWriter class name is too close to
 * 	the already-existing SpecTraceExpressionWriter class name.
 * 
 * This is the spec writer concrete class which has niceties that lend themselves to the creation of the "TE" tla/cfg
 * 	pair.
 */
public class TraceExpressionExplorerSpecWriter extends AbstractSpecWriter {
	private static final String EXPRESSION_VARIABLE_NAME_PREFIX = "_traceExpression_";
	private static final String EXPRESSION_COMMENT_LINE_PREFIX = TLAConstants.COMMENT + " TRACE EXPRESSION: ";
	
    private static final String TE_INIT_ID = "_TEInit";
    private static final String TE_INIT_ATTRIBUTE_NAME = "teBehaviorInit";
    private static final String TE_NEXT_ID = "_TENext";
    private static final String TE_NEXT_ATTRIBUTE_NAME = "teBehaviorNext";
    
    /**
     * If the TLA file exists, it will be examined; if it is found to have been generated by this writer, a
     * 	map of variableName -> traceExpression will be returned. Otherwise null will be returned.
     * 
     * @param tlaFile
     * @return a map of variableName -> traceExpression if the file exists and was created by this writer, else null.
     */
    public static HashMap<String, String> getVariableExpressionMapFromTLAFile(final File tlaFile) throws IOException {
    	if (tlaFile.exists()) {
    		try (final BufferedReader br = new BufferedReader(new FileReader(tlaFile))) {
    			final ArrayList<String> declarations = new ArrayList<>();
    			boolean foundLine = true;
    			String line;
    			
    			while (foundLine && ((line = br.readLine()) != null)) {
    				if (line.startsWith(EXPRESSION_COMMENT_LINE_PREFIX)) {
    					declarations.add(line.substring(EXPRESSION_COMMENT_LINE_PREFIX.length()));
    				} else {
    					foundLine = false;
    				}
    			}

    			if (declarations.size() > 0) {
    				final HashMap<String, String> variableExpressionMap = new HashMap<>();
    				
    				for (final String declaration : declarations) {
    					final int index = declaration.indexOf(TLAConstants.EQ);
    					if (index != -1) {
        					final String variable = declaration.substring(0, index);
        					final String expression = declaration.substring(index + TLAConstants.EQ.length());

        					variableExpressionMap.put(variable, expression);
    					}
    				}
    				
    				return variableExpressionMap;
    			}
    		}
    	}
    	
    	return null;
    }
    

    private final TreeMap<String, String> variableExpressionMap;
    
	TraceExpressionExplorerSpecWriter(final List<String> expressions) {
		super(true);
		
		variableExpressionMap = new TreeMap<>();
		int count = 1;
		for (final String expression : expressions) {
			final String key = EXPRESSION_VARIABLE_NAME_PREFIX + count;
			variableExpressionMap.put(key, expression);
			tlaBuffer.append(EXPRESSION_COMMENT_LINE_PREFIX).append(key).append(TLAConstants.EQ);
			tlaBuffer.append(expression).append(TLAConstants.CR);
			count++;
		}
		
		addPrimer(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME,
				  TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME);
		
		declareExpressionVariables();
		createInitNextWithExpressions();
		
		tlaBuffer.append(SpecWriterUtilities.getGeneratedTimeStampCommentLine()).append(TLAConstants.CR);
	}
	
	StringBuilder getConfigBuffer() {
		return cfgBuffer;
	}
	
	private void declareExpressionVariables() {
		tlaBuffer.append("VARIABLES ");

		boolean notFirst = false;
		for (final String variable : variableExpressionMap.keySet()) {
			if (notFirst) {
				tlaBuffer.append(", ");
			} else {
				notFirst = true;
			}
			
			tlaBuffer.append(variable);
		}
		
		tlaBuffer.append(TLAConstants.CR).append(TLAConstants.CR);
	}
	
    static final String SPEC_TE_INIT_ID = "_SpecTEInit";
    static final String SPEC_TE_NEXT_ID = "_SpecTENext";
	
	private void createInitNextWithExpressions() {
		final StringBuilder initConjunction = new StringBuilder(TLAConstants.INDENTED_CONJUNCTIVE);
		initConjunction.append(SPEC_TE_INIT_ID).append(TLAConstants.CR);
		addExpressionsToBuffer(initConjunction, false);
		
		final List<String[]> initContent
						= SpecWriterUtilities.createSourceContent(initConjunction.toString(), TE_INIT_ID, false);
		addFormulaList(initContent, TLAConstants.KeyWords.INIT, TE_INIT_ATTRIBUTE_NAME);
		
		
		final StringBuilder nextConjunction = new StringBuilder(TLAConstants.INDENTED_CONJUNCTIVE);
		nextConjunction.append(SPEC_TE_NEXT_ID).append(TLAConstants.CR);
		addExpressionsToBuffer(nextConjunction, true);

		final List<String[]> nextContent
						= SpecWriterUtilities.createSourceContent(nextConjunction.toString(), TE_NEXT_ID, false);
		addFormulaList(nextContent, TLAConstants.KeyWords.NEXT, TE_NEXT_ATTRIBUTE_NAME);
	}
	
	private void addExpressionsToBuffer(final StringBuilder buffer, final boolean primed) {
		for (final Map.Entry<String, String> me : variableExpressionMap.entrySet()) {
			buffer.append(TLAConstants.INDENTED_CONJUNCTIVE).append(me.getKey());
			if (primed) {
				buffer.append(TLAConstants.PRIME);
			}
			buffer.append(TLAConstants.EQ);
			buffer.append(TLAConstants.L_PAREN).append(me.getValue()).append(TLAConstants.R_PAREN);
			buffer.append(TLAConstants.CR);
		}
	}
}
