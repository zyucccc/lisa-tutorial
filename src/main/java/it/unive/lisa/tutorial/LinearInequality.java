package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Map;
import java.util.function.Predicate;

//--------------------------------   ax + by ≤ c  -------------------------------//
public class LinearInequality implements ValueDomain<LinearInequality> {
    private final Identifier var1; // var: X
    private final double coeff1;   // coeff: a
    private final Identifier var2; // var: Y
    private final double coeff2;   // coeff: b
    private final double constant; // constant: c

    private final boolean isTop;
    private final boolean isBottom;

    public LinearInequality(Identifier var1, double coeff1, Identifier var2, double coeff2, double constant) {
        this.var1 = var1;
        this.coeff1 = coeff1;
        this.var2 = var2;
        this.coeff2 = coeff2;
        this.constant = constant;
        this.isTop = false;
        this.isBottom = false;
    }

    private LinearInequality(boolean isTop, boolean isBottom) {
        this.var1 = null;
        this.coeff1 = 0;
        this.var2 = null;
        this.coeff2 = 0;
        this.constant = 0;
        this.isTop = isTop;
        this.isBottom = isBottom;
    }

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////                            Getter                              ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    public Identifier getVar1() {
        return var1;
    }

    public double getCoeff1() {
        return coeff1;
    }

    public Identifier getVar2() {
        return var2;
    }

    public double getCoeff2() {
        return coeff2;
    }

    public double getConstant() {
        return constant;
    }

    public boolean isTop() {
        return isTop;
    }

    public boolean isBottom() {
        return isBottom;
    }

    @Override
    public boolean lessOrEqual(LinearInequality linearInequality) throws SemanticException {
        return false;
    }

    @Override
    public LinearInequality lub(LinearInequality linearInequality) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality top() {
        return null;
    }

    @Override
    public LinearInequality bottom() {
        return null;
    }

    @Override
    public LinearInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality assume(ValueExpression valueExpression, ProgramPoint programPoint, ProgramPoint programPoint1, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return false;
    }

    @Override
    public LinearInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        return null;
    }

    @Override
    public Satisfiability satisfies(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return null;
    }

    @Override
    public LinearInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return null;
    }

    @Override
    public StructuredRepresentation representation() {
        return null;
    }
}
