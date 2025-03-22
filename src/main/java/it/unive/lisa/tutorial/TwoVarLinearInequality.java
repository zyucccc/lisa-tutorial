package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.lattices.SetLattice;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.util.representation.StructuredRepresentation;
import it.unive.lisa.analysis.lattices.FunctionalLattice;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

//--------------------------------   ax + by ≤ c  -------------------------------//
public class TwoVarLinearInequality extends FunctionalLattice<TwoVarLinearInequality, Identifier, TwoVarLinearInequality.SetOfInequalities> implements ValueDomain<TwoVarLinearInequality> {

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////     a single inequality(equation) of the form ax + by ≤ c      ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    public static class LinearInequality {
        private final Identifier var1; // var: X
        private final double coeff1;   // coeff: a
        private final Identifier var2; // var: Y
        private final double coeff2;   // coeff: b
        private final double constant; // constant: c

        public LinearInequality(Identifier var1, double coeff1, Identifier var2, double coeff2, double constant) {
            this.var1 = var1;
            this.coeff1 = coeff1;
            this.var2 = var2;
            this.coeff2 = coeff2;
            this.constant = constant;
        }

        //----------------------  Getter  ----------------------//
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

        //Returns the set of variables present in this inequality : (x,y)
        public Set<Identifier> getVariables() {
            Set<Identifier> vars = new HashSet<>();
            if (var1 != null && coeff1 != 0) vars.add(var1);
            if (var2 != null && coeff2 != 0) vars.add(var2);
            return vars;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null || getClass() != obj.getClass())
                return false;

            LinearInequality other = (LinearInequality) obj;

            // Compare variables and coefficients
            if (this.var1 == null ? other.var1 != null : !this.var1.equals(other.var1))
                return false;
            if (this.var2 == null ? other.var2 != null : !this.var2.equals(other.var2))
                return false;

            return Double.compare(this.coeff1, other.coeff1) == 0 &&
                    Double.compare(this.coeff2, other.coeff2) == 0 &&
                    Double.compare(this.constant, other.constant) == 0;
        }

        @Override
        public int hashCode() {
            int result = 1;
            result = 31 * result + (var1 == null ? 0 : var1.hashCode());
            result = 31 * result + (var2 == null ? 0 : var2.hashCode());
            result = 31 * result + Double.hashCode(coeff1);
            result = 31 * result + Double.hashCode(coeff2);
            result = 31 * result + Double.hashCode(constant);
            return result;
        }

        //to_string: ax + by ≤ c
        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();

            boolean hasTerms = false;

            // Format var1 term
            if (var1 != null && coeff1 != 0) {
                if (coeff1 != 1) {
                    sb.append(coeff1);
                }
                sb.append(var1);
                hasTerms = true;
            }

            // Format var2 term
            if (var2 != null && coeff2 != 0) {
                if (hasTerms) {
                    if (coeff2 > 0) {
                        sb.append(" + ");
                    } else {
                        sb.append(" - ");
                    }

                    if (Math.abs(coeff2) != 1) {
                        sb.append(Math.abs(coeff2));
                    }
                } else {
                    if (coeff2 != 1) {
                        sb.append(coeff2);
                    }
                }

                sb.append(var2);
                hasTerms = true;
            }

            // Add inequality symbol
            sb.append(" ≤ ");

            // Add constant
            sb.append(constant);

            return sb.toString();
        }
    }

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////          a set of inequalities,the mapping: Two_X → R^n        ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    public static class SetOfInequalities extends SetLattice<SetOfInequalities, TwoVarLinearInequality> {
        public SetOfInequalities(Set<TwoVarLinearInequality> elements, boolean isTop) {
            super(elements, isTop);
        }

        @Override
        public SetOfInequalities mk(Set<TwoVarLinearInequality> set) {
            return new SetOfInequalities(set, set.isEmpty());
        }

        @Override
        public SetOfInequalities top() {
            return new SetOfInequalities(Collections.emptySet(), true);
        }

        @Override
        public SetOfInequalities bottom() {
            return new SetOfInequalities(Collections.emptySet(), false);
        }
    }

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////            TwoVarLinearInequality : Constructor                ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    public TwoVarLinearInequality(SetOfInequalities lattice, Map<Identifier, SetOfInequalities> function) {
        super(lattice, function);
    }

    public TwoVarLinearInequality(SetOfInequalities lattice) {
        super(lattice);
    }

    public TwoVarLinearInequality() {
        super(new SetOfInequalities(Collections.emptySet(), true));
    }



    @Override
    public SetOfInequalities stateOfUnknown(Identifier identifier) {
        return null;
    }

    @Override
    public TwoVarLinearInequality mk(SetOfInequalities twoVarLinearInequalities, Map<Identifier, SetOfInequalities> map) {
        return null;
    }


    public TwoVarLinearInequality top() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), true), null);
    }


    public TwoVarLinearInequality bottom() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), false), null);
    }

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////                            Lattice                             ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    //-------------------------   Least upper bound   -------------------------------//
    @Override
    public TwoVarLinearInequality lub(TwoVarLinearInequality other) throws SemanticException {
        if (this.isBottom())
            return other;
        if (other.isBottom())
            return this;
        if (this.isTop() || other.isTop())
            return top();

        return null;
    }

    @Override
    public boolean lessOrEqual(TwoVarLinearInequality twoVarLinearInequality) throws SemanticException {
        return false;
    }

    @Override
    public TwoVarLinearInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public TwoVarLinearInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public TwoVarLinearInequality assume(ValueExpression valueExpression, ProgramPoint programPoint, ProgramPoint programPoint1, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return false;
    }

    @Override
    public TwoVarLinearInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        return null;
    }

    @Override
    public TwoVarLinearInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        return null;
    }

    @Override
    public Satisfiability satisfies(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return null;
    }

    @Override
    public TwoVarLinearInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return null;
    }

    @Override
    public TwoVarLinearInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return null;
    }

    @Override
    public StructuredRepresentation representation() {
        return null;
    }
}
