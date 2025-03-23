package it.unive.lisa.tutorial;

import it.unive.lisa.AnalysisException;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.LiSA;
import it.unive.lisa.analysis.heap.pointbased.FieldSensitivePointBasedHeap;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.conf.LiSAConfiguration.GraphType;
import it.unive.lisa.imp.IMPFrontend;
import it.unive.lisa.imp.ParsingException;
import it.unive.lisa.program.Program;
import org.junit.Test;

public class TwoVarLinearInequalityTest {

    @Test
    public void testTwoVarLinearInequality() throws ParsingException, AnalysisException {
        Program program = IMPFrontend.processFile("inputs/twoVarPerLinearInequality.imp");

        LiSAConfiguration conf = new DefaultConfiguration();

        conf.workdir = "outputs/twoVarPerLinearInequality";

        conf.analysisGraphs = GraphType.HTML;

        conf.abstractState = DefaultConfiguration.simpleState(
                new FieldSensitivePointBasedHeap(),
                new TwoVarLinearInequality(),
                DefaultConfiguration.defaultTypeDomain());

        LiSA lisa = new LiSA(conf);

        lisa.run(program);
    }
}