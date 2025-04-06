package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.lattices.SetLattice;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.outputs.serializableGraph.SerializableObject;
import it.unive.lisa.outputs.serializableGraph.SerializableValue;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.util.representation.StringRepresentation;
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
    ////              a set of inequalities,the mapping                 ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    public static class SetOfInequalities extends SetLattice<SetOfInequalities, LinearInequality> {
        public SetOfInequalities(Set<LinearInequality> elements, boolean isTop) {
            super(elements, isTop);
        }

        @Override
        public SetOfInequalities mk(Set<LinearInequality> set) {
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

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////              TwoVarLinearInequality : Lattice                  ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    @Override
    public TwoVarLinearInequality lub(TwoVarLinearInequality other) throws SemanticException {
        if (this.isBottom())
            return other;
        if (other.isBottom())
            return this;
        if (this.isTop() || other.isTop())
            return top();

        Set<LinearInequality> allInequalities = new HashSet<>();
        //union des deux ensembles cl(conv([T1] ∪ [T2]))
        //Union:[T1] ∪ [T2]
        // collect all inequalities from this
        for (Identifier id : this.getKeys()) {
            allInequalities.addAll(this.getState(id).elements);
        }
        // collect all inequalities from other
        for (Identifier id : other.getKeys()) {
            allInequalities.addAll(other.getState(id).elements);
        }

        //closure
        Set<LinearInequality> result = close(allInequalities);

        // return the new lattice
        return createDomainFromInequalities(result);
    }

    //----------------------- Filter for closure,Paper: definition 8 -------------------------------//
    //remove redundant inequalities
    // "simplifier"
    private Set<LinearInequality> filter(Set<LinearInequality> inequalities) {
        // :check si y a : 0x + 0y ≤ -1
        for (LinearInequality ineq : inequalities) {
            if (Math.abs(ineq.getCoeff1()) < 1e-10 &&
                    Math.abs(ineq.getCoeff2()) < 1e-10 &&
                    ineq.getConstant() < -1e-10) {
                // insatisfiable
                Set<LinearInequality> result = new HashSet<>();
                result.add(ineq);
                return result;
            }
        }

        return new HashSet<>(inequalities);
    }

    //----------------------- Result for closure,Paper: definition 9 -------------------------------//
    private Set<LinearInequality> result(Set<LinearInequality> inequalities) {
        Set<LinearInequality> resultSet = new HashSet<>();

        // 2 fois boucle pour chaque paire de inequalities
        for (LinearInequality t1 : inequalities) {
            for (LinearInequality t2 : inequalities) {
                if (t1 == t2) continue;

                // check if the variables are null
                if (t1.getVar1() == null || t2.getVar1() == null) {
                    continue;
                }

                boolean var2Equal = false;
                if (t1.getVar2() == null && t2.getVar2() == null) {
                    var2Equal = true;
                } else if (t1.getVar2() != null && t2.getVar2() != null && t1.getVar2().equals(t2.getVar2())) {
                    var2Equal = true;
                }

                if (!var2Equal) {
                    continue;
                }

                // same variables
//                if (!t1.getVar1().equals(t2.getVar1()) ||
//                        !t1.getVar2().equals(t2.getVar2())) {
//                    continue;
//                }

                double a = t1.getCoeff1();
                double b = t1.getCoeff2();
                double c = t1.getConstant();

                double d = t2.getCoeff1();
                double e = t2.getCoeff2();
                double f = t2.getConstant();

                if (a > 0 && d < 0) {
                    // new inequality: aez - dby ≤ af - dc
                    double newCoeffZ = a * e;
                    double newCoeffY = -d * b;
                    double newConstant = a * f - d * c;

                    LinearInequality newIneq = new LinearInequality(
                            t1.getVar1(), newCoeffY,
                            t1.getVar2(), newCoeffZ,
                            newConstant
                    );

                    resultSet.add(newIneq);
                }
            }
        }

        return resultSet;
    }

    //------------------------------- closure,Paper: definition 9 -------------------------------//
    private Set<LinearInequality> close(Set<LinearInequality> inequalities) {
        // collect all variables
        Set<Identifier> vars = new HashSet<>();
        for (LinearInequality ineq : inequalities) {
            vars.addAll(ineq.getVariables());
        }

        if (vars.size() <= 1) {
            return inequalities;
        }

        // calculate the number of iterations
        int iterations = (int) Math.floor(Math.log(vars.size() - 1) / Math.log(2));
        iterations = Math.max(iterations, 1);

        // definition 10
        Set<LinearInequality> current = new HashSet<>(inequalities);
        // log2(n-1) iterations
        for (int i = 0; i < iterations; i++) {
            Set<LinearInequality> resultSet = result(current);
            Set<LinearInequality> union = new HashSet<>(current);
            union.addAll(resultSet);
            current = filter(union);

            //if find invalid inequality,return
            for (LinearInequality ineq : current) {
                //1e-10 bias for float
                if (Math.abs(ineq.getCoeff1()) < 1e-10 &&
                        Math.abs(ineq.getCoeff2()) < 1e-10 &&
                        ineq.getConstant() < 0) {
                    return current;
                }
            }
        }

        return current;
    }

    @Override
    public boolean lessOrEqual(TwoVarLinearInequality other) throws SemanticException {
        if (this.isBottom())
            return true;
        if (other.isBottom())
            return this.isBottom();
        if (this.isTop())
            return other.isTop();
        if (other.isTop())
            return true;

        // collect all inequalities from this
        Set<LinearInequality> thisInequalities = new HashSet<>();
        for (Identifier id : this.getKeys()) {
            thisInequalities.addAll(this.getState(id).elements);
        }

        // check if all inequalities from this are entailed by other
        for (LinearInequality inequality : thisInequalities) {
            if (!entails(other, inequality)) {
                return false;
            }
        }

        return true;
    }

    private boolean entails(TwoVarLinearInequality system, LinearInequality inequality) {
        // collect all inequalities from system
        Set<LinearInequality> systemInequalities = new HashSet<>();
        for (Identifier id : system.getKeys()) {
            systemInequalities.addAll(system.getState(id).elements);
        }

        // if the inequality is already in the system, it is entailed
        if (systemInequalities.contains(inequality)) {
            return true;
        }

        // Paper: Proposition 2 - Cramer rule
        double a1 = inequality.getCoeff1();
        double b1 = inequality.getCoeff2();
        double c1 = inequality.getConstant();

        for (LinearInequality ineq : systemInequalities) {
            double a = ineq.getCoeff1();
            double b = ineq.getCoeff2();
            double c = ineq.getConstant();

            // check if ils ont les mêmes variables
//            if (!inequality.getVar1().equals(ineq.getVar1()) ||
//                    !inequality.getVar2().equals(ineq.getVar2())) {
//                continue;
//            }
            boolean var1Equal = false;
            boolean var2Equal = false;

            if (inequality.getVar1() == null && ineq.getVar1() == null) {
                var1Equal = true;
            } else if (inequality.getVar1() != null && ineq.getVar1() != null &&
                    inequality.getVar1().equals(ineq.getVar1())) {
                var1Equal = true;
            }

            if (inequality.getVar2() == null && ineq.getVar2() == null) {
                var2Equal = true;
            } else if (inequality.getVar2() != null && ineq.getVar2() != null &&
                    inequality.getVar2().equals(ineq.getVar2())) {
                var2Equal = true;
            }

            if (!var1Equal || !var2Equal) {
                continue;
            }

            if(a1*b - a*b1 != 0) {
               return false;
            }else if(a1*a < 0 || b1*b < 0) {
                return false;
            }else if(a1 != 0){
                return ((a/a1)*c1) <= c;
            } else if (b1 != 0) {
                return ((b/b1)*c1) <= c;
            } else {
                return (c1<0) || (c>=0 && a==0 && b==0);
            }

        }

        return false;
    }


    private TwoVarLinearInequality createDomainFromInequalities(Set<LinearInequality> inequalities) {
        TwoVarLinearInequality result = new TwoVarLinearInequality();

        // mapping for variables -> inequalities
        // ex:
        // x + y ≤ 10
        // x - z ≤ 5
        // y + z ≤ 8
        // x → {x + y ≤ 10, x - z ≤ 5}
        // y → {x + y ≤ 10, y + z ≤ 8}
        // z → {x - z ≤ 5, y + z ≤ 8}
        for (LinearInequality ineq : inequalities) {
            for (Identifier var : ineq.getVariables()) {
                SetOfInequalities varState = result.getState(var);
                Set<LinearInequality> currentInequalities = new HashSet<>(varState.elements);

                // add the new inequality
                currentInequalities.add(ineq);

                // update the mapping
                result = result.putState(var, new SetOfInequalities(currentInequalities, false));
            }
        }

        return result;
    }



    @Override
    public SetOfInequalities stateOfUnknown(Identifier identifier) {
        return new SetOfInequalities(Collections.emptySet(), true);
    }

    @Override
    public TwoVarLinearInequality mk(SetOfInequalities setOfInequalities, Map<Identifier, SetOfInequalities> map) {
        return new TwoVarLinearInequality(setOfInequalities, map);
    }


    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////                            Lattice                             ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    //-------------------------   Least upper bound   -------------------------------//

    public TwoVarLinearInequality top() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), true), null);
    }


    public TwoVarLinearInequality bottom() {
        return new TwoVarLinearInequality(new SetOfInequalities(Collections.emptySet(), false), null);
    }

    @Override
    public TwoVarLinearInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        // if a variable is reassigned, it can no longer be an upperbound of other variables
        // so we need to forget the variable from the state firstly
        TwoVarLinearInequality result = this.forgetIdentifier(identifier);

        if (valueExpression instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression) valueExpression;
            BinaryOperator op = be.getOperator();

            //  id = x + c // id = x - c
            if (be.getLeft() instanceof Identifier && be.getRight() instanceof Constant) {
                Identifier var = (Identifier) be.getLeft();
                Constant c = (Constant) be.getRight();

                // instantiate new inequality
                if (c.getValue() instanceof Number) {
                    double constValue = ((Number) c.getValue()).doubleValue();

                    //  id ≤ var + const
                    LinearInequality ineq1 = new LinearInequality(
                            identifier, 1.0,
                            var, -1.0,
                            constValue
                    );

                    // var ≤ id + const
                    LinearInequality ineq2 = new LinearInequality(
                            var, 1.0,
                            identifier, -1.0,
                            constValue
                    );

                    // push state
                    Set<LinearInequality> newIneqs = new HashSet<>();
                    newIneqs.add(ineq1);
                    newIneqs.add(ineq2);

                    // update mappings
                    result = result.putState(identifier, new SetOfInequalities(newIneqs, false));
                    result = result.putState(var, new SetOfInequalities(newIneqs, false));
                }
            }

            //  id = const
            if (be.getLeft() instanceof Constant) {
                Constant c = (Constant) be.getLeft();
                if (c.getValue() instanceof Number) {
                    double constValue = ((Number) c.getValue()).doubleValue();

                    // for assigning constant for var, we instantiate id ≤ const && -id ≤ -const
                    //  id == const
                    LinearInequality ineq1 = new LinearInequality(
                            identifier, 1.0,
                            null, 0.0,
                            constValue
                    );

                    LinearInequality ineq2 = new LinearInequality(
                            identifier, -1.0,
                            null, 0.0,
                            -constValue
                    );

                    Set<LinearInequality> newIneqs = new HashSet<>();
                    newIneqs.add(ineq1);
                    newIneqs.add(ineq2);

                    result = result.putState(identifier, new SetOfInequalities(newIneqs, false));
                }
            }
        }

        //  id = x
        if (valueExpression instanceof Identifier) {
            Identifier var = (Identifier) valueExpression;

            // instantiate id ≤ var && var ≤ id 不等式
            LinearInequality ineq1 = new LinearInequality(
                    identifier, 1.0,
                    var, -1.0,
                    0.0
            );

            LinearInequality ineq2 = new LinearInequality(
                    var, 1.0,
                    identifier, -1.0,
                    0.0
            );

            Set<LinearInequality> newIneqs = new HashSet<>();
            newIneqs.add(ineq1);
            newIneqs.add(ineq2);

            result = result.putState(identifier, new SetOfInequalities(newIneqs, false));
            result = result.putState(var, new SetOfInequalities(newIneqs, false));
        }

        return createDomainFromInequalities(close(getAllInequalities(result)));
    }

    @Override
    public TwoVarLinearInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return this;
    }

    //if (cond)
    @Override
    public TwoVarLinearInequality assume(ValueExpression valueExpression, ProgramPoint programPoint, ProgramPoint programPoint1, SemanticOracle semanticOracle) throws SemanticException {
        if (!(valueExpression instanceof BinaryExpression))
            return this;

        BinaryExpression bexp = (BinaryExpression) valueExpression;
        SymbolicExpression left = bexp.getLeft();
        SymbolicExpression right = bexp.getRight();
        BinaryOperator operator = bexp.getOperator();

        // 1. x ≤ y (ou x < y, x > y, x ≥ y)
        // 2. x ≤ c

        // comparison between two variables
        if (left instanceof Identifier && right instanceof Identifier) {
            Identifier x = (Identifier) left;
            Identifier y = (Identifier) right;

            if (operator instanceof ComparisonLt || operator instanceof ComparisonLe) {
                // x ≤ y ou x < y，instantiate x - y ≤ 0
                LinearInequality ineq = new LinearInequality(
                        x, 1.0,
                        y, -1.0,
                        0.0
                );

                //its like we add a new constraint in our system (set of inequalities)
                Set<LinearInequality> constraints = new HashSet<>();
                constraints.add(ineq);

                // update mappings
                TwoVarLinearInequality result = this;
                result = result.putState(x, new SetOfInequalities(
                        addInequality(result.getState(x).elements, ineq), false));
                result = result.putState(y, new SetOfInequalities(
                        addInequality(result.getState(y).elements, ineq), false));

                return createDomainFromInequalities(close(getAllInequalities(result)));
            } else if (operator instanceof ComparisonGt || operator instanceof ComparisonGe) {
                // x > y ou x ≥ y，instantiate y - x ≤ 0
                LinearInequality ineq = new LinearInequality(
                        y, 1.0,
                        x, -1.0,
                        0.0
                );

                // add new constraint
                Set<LinearInequality> constraints = new HashSet<>();
                constraints.add(ineq);

                // mapping
                TwoVarLinearInequality result = this;
                result = result.putState(x, new SetOfInequalities(
                        addInequality(result.getState(x).elements, ineq), false));
                result = result.putState(y, new SetOfInequalities(
                        addInequality(result.getState(y).elements, ineq), false));

                return createDomainFromInequalities(close(getAllInequalities(result)));
            } else if (operator instanceof ComparisonEq) {
                // x == y，instantiate x - y ≤ 0 && y - x ≤ 0
                LinearInequality ineq1 = new LinearInequality(
                        x, 1.0,
                        y, -1.0,
                        0.0
                );

                LinearInequality ineq2 = new LinearInequality(
                        y, 1.0,
                        x, -1.0,
                        0.0
                );

                Set<LinearInequality> constraints = new HashSet<>();
                constraints.add(ineq1);
                constraints.add(ineq2);

                TwoVarLinearInequality result = this;
                result = result.putState(x, new SetOfInequalities(
                        addInequalities(result.getState(x).elements, constraints), false));
                result = result.putState(y, new SetOfInequalities(
                        addInequalities(result.getState(y).elements, constraints), false));

                return createDomainFromInequalities(close(getAllInequalities(result)));
            }
        }

        // comparison between a variable and a constant
        if (left instanceof Identifier && right instanceof Constant) {
            Identifier x = (Identifier) left;
            Constant c = (Constant) right;

            if (c.getValue() instanceof Number) {
                double constValue = ((Number) c.getValue()).doubleValue();

                if (operator instanceof ComparisonLt || operator instanceof ComparisonLe) {
                    // x ≤ c ou x < c，instantiate x ≤ c
                    LinearInequality ineq = new LinearInequality(
                            x, 1.0,
                            null, 0.0,
                            constValue
                    );

                    Set<LinearInequality> constraints = new HashSet<>();
                    constraints.add(ineq);

                    TwoVarLinearInequality result = this;
                    result = result.putState(x, new SetOfInequalities(
                            addInequality(result.getState(x).elements, ineq), false));

                    return createDomainFromInequalities(close(getAllInequalities(result)));
                } else if (operator instanceof ComparisonGt || operator instanceof ComparisonGe) {
                    // x > c ou x ≥ c，instantiate -x ≤ -c
                    LinearInequality ineq = new LinearInequality(
                            x, -1.0,
                            null, 0.0,
                            -constValue
                    );

                    Set<LinearInequality> constraints = new HashSet<>();
                    constraints.add(ineq);

                    TwoVarLinearInequality result = this;
                    result = result.putState(x, new SetOfInequalities(
                            addInequality(result.getState(x).elements, ineq), false));

                    return createDomainFromInequalities(close(getAllInequalities(result)));
                } else if (operator instanceof ComparisonEq) {
                    // x == c，instantiate x ≤ c && -x ≤ -c
                    LinearInequality ineq1 = new LinearInequality(
                            x, 1.0,
                            null, 0.0,
                            constValue
                    );

                    LinearInequality ineq2 = new LinearInequality(
                            x, -1.0,
                            null, 0.0,
                            -constValue
                    );

                    Set<LinearInequality> constraints = new HashSet<>();
                    constraints.add(ineq1);
                    constraints.add(ineq2);

                    TwoVarLinearInequality result = this;
                    result = result.putState(x, new SetOfInequalities(
                            addInequalities(result.getState(x).elements, constraints), false));

                    return createDomainFromInequalities(close(getAllInequalities(result)));
                }
            }
        }

        // reverse the comparison for adverse comparison
        if (right instanceof Identifier && left instanceof Constant) {
            return assume(
                    new BinaryExpression(
                            valueExpression.getStaticType(),
                            right,
                            left,
                            reverseOperator(operator),
                            valueExpression.getCodeLocation()),
                    programPoint,
                    programPoint1,
                    semanticOracle);
        }

        return this;
    }

    private BinaryOperator reverseOperator(BinaryOperator op) {
        if (op instanceof ComparisonLt)
            return ComparisonGt.INSTANCE;
        if (op instanceof ComparisonLe)
            return ComparisonGe.INSTANCE;
        if (op instanceof ComparisonGt)
            return ComparisonLt.INSTANCE;
        if (op instanceof ComparisonGe)
            return ComparisonLe.INSTANCE;
        return op;
    }

    private Set<LinearInequality> addInequality(Set<LinearInequality> set, LinearInequality ineq) {
        Set<LinearInequality> result = new HashSet<>(set);
        result.add(ineq);
        return result;
    }

    private Set<LinearInequality> addInequalities(Set<LinearInequality> set, Set<LinearInequality> ineqs) {
        Set<LinearInequality> result = new HashSet<>(set);
        result.addAll(ineqs);
        return result;
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return this.getKeys().contains(identifier);
    }

    @Override
    public TwoVarLinearInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        TwoVarLinearInequality result = this;

        // remove the identifier(variable) from the mapping
        if (result.getKeys().contains(identifier)) {
            result = result.putState(identifier, new SetOfInequalities(Collections.emptySet(), true));
        }

        // remove all inequalities that contain the identifier
        Set<Identifier> allIdentifiers = new HashSet<>(result.getKeys());
        for (Identifier id : allIdentifiers) {
            Set<LinearInequality> updatedInequalities = new HashSet<>();
            boolean hasChanged = false;

            for (LinearInequality ineq : result.getState(id).elements) {
                if (!ineq.getVariables().contains(identifier)) {
                    updatedInequalities.add(ineq);
                } else {
                    hasChanged = true;
                }
            }

            if (hasChanged) {
                result = result.putState(id, new SetOfInequalities(updatedInequalities, updatedInequalities.isEmpty()));
            }
        }

        return result;
    }

    @Override
    public TwoVarLinearInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        TwoVarLinearInequality result = this;

        // collect all identifiers that satisfy the predicate
        Set<Identifier> toForget = new HashSet<>();
        for (Identifier id : this.getKeys()) {
            if (predicate.test(id)) {
                toForget.add(id);
            }
        }

        for (Identifier id : toForget) {
            result = result.forgetIdentifier(id);
        }

        return result;
    }

    //-----------------------  Get all inequalities from TWOx  ----------------------//
    private Set<LinearInequality> getAllInequalities(TwoVarLinearInequality domain) {
        Set<LinearInequality> allInequalities = new HashSet<>();
        for (Identifier id : domain.getKeys()) {
            allInequalities.addAll(domain.getState(id).elements);
        }
        return allInequalities;
    }

    @Override
    public Satisfiability satisfies(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        if (this.isBottom())
            return Satisfiability.BOTTOM;

        // si l'expression n'est pas une expression binaire,x,y,on ne peut pas la traiter
        if (!(valueExpression instanceof BinaryExpression))
            return Satisfiability.UNKNOWN;

        BinaryExpression bexp = (BinaryExpression) valueExpression;
        SymbolicExpression left = bexp.getLeft();
        SymbolicExpression right = bexp.getRight();
        BinaryOperator operator = bexp.getOperator();

        // compare two variables
        if (left instanceof Identifier && right instanceof Identifier) {
            Identifier x = (Identifier) left;
            Identifier y = (Identifier) right;

            // for x ≤ y
            if (operator instanceof ComparisonLe || operator instanceof ComparisonLt) {
                // check if  x - y ≤ c， c ≤ 0 exists -> x ≤ y exists
                for (LinearInequality ineq : getAllInequalities(this)) {
                    if (ineq.getVar1() != null && ineq.getVar2() != null &&
                            ineq.getVar1().equals(x) && ineq.getVar2().equals(y) &&
                            Math.abs(ineq.getCoeff1() - 1.0) < 1e-10 &&
                            Math.abs(ineq.getCoeff2() + 1.0) < 1e-10 &&
                            ineq.getConstant() <= 0) {
                        return Satisfiability.SATISFIED;
                    }
                }
            }

            //  x ≥ y ou x > y
            if (operator instanceof ComparisonGe || operator instanceof ComparisonGt) {
                // check if y - x ≤ c , c ≤ 0  -> x ≥ y ou x > y
                for (LinearInequality ineq : getAllInequalities(this)) {
                    if (ineq.getVar1() != null && ineq.getVar2() != null &&
                            ineq.getVar1().equals(y) && ineq.getVar2().equals(x) &&
                            Math.abs(ineq.getCoeff1() - 1.0) < 1e-10 &&
                            Math.abs(ineq.getCoeff2() + 1.0) < 1e-10 &&
                            ineq.getConstant() <= 0) {
                        return Satisfiability.SATISFIED;
                    }
                }
            }

            //  x == y
            if (operator instanceof ComparisonEq) {
                // x ≤ y + y ≤ x
                boolean xLessEqY = false;
                boolean yLessEqX = false;

                for (LinearInequality ineq : getAllInequalities(this)) {
                    if (ineq.getVar1() != null && ineq.getVar2() != null) {
                        //  x - y ≤ 0 ->x ≤ y
                        if (ineq.getVar1().equals(x) && ineq.getVar2().equals(y) &&
                                Math.abs(ineq.getCoeff1() - 1.0) < 1e-10 &&
                                Math.abs(ineq.getCoeff2() + 1.0) < 1e-10 &&
                                ineq.getConstant() <= 0) {
                            xLessEqY = true;
                        }

                        // y-x<=0 -> y - x ≤ 0
                        if (ineq.getVar1().equals(y) && ineq.getVar2().equals(x) &&
                                Math.abs(ineq.getCoeff1() - 1.0) < 1e-10 &&
                                Math.abs(ineq.getCoeff2() + 1.0) < 1e-10 &&
                                ineq.getConstant() <= 0) {
                            yLessEqX = true;
                        }
                    }
                }

                if (xLessEqY && yLessEqX)
                    return Satisfiability.SATISFIED;
            }
        }

        // compare variable and constant
        if (left instanceof Identifier && right instanceof Constant) {
            Identifier x = (Identifier) left;
            Constant c = (Constant) right;

            if (c.getValue() instanceof Number) {
                double constValue = ((Number) c.getValue()).doubleValue();

                if (operator instanceof ComparisonLe || operator instanceof ComparisonLt) {
                    //  x ≤ c
                    for (LinearInequality ineq : getAllInequalities(this)) {
                        if (ineq.getVar1() != null && ineq.getVar1().equals(x) &&
                                (ineq.getVar2() == null || Math.abs(ineq.getCoeff2()) < 1e-10) &&
                                Math.abs(ineq.getCoeff1() - 1.0) < 1e-10 &&
                                ineq.getConstant() <= constValue) {
                            return Satisfiability.SATISFIED;
                        }
                    }
                }

                if (operator instanceof ComparisonGe || operator instanceof ComparisonGt) {
                    //  x ≥ c ou -x ≤ -c
                    for (LinearInequality ineq : getAllInequalities(this)) {
                        if (ineq.getVar1() != null && ineq.getVar1().equals(x) &&
                                (ineq.getVar2() == null || Math.abs(ineq.getCoeff2()) < 1e-10) &&
                                Math.abs(ineq.getCoeff1() + 1.0) < 1e-10 &&
                                ineq.getConstant() <= -constValue) {
                            return Satisfiability.SATISFIED;
                        }
                    }
                }
            }
        }

        return Satisfiability.UNKNOWN;
    }

    @Override
    public TwoVarLinearInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    @Override
    public TwoVarLinearInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }


//    @Override
//    public StructuredRepresentation representation() {
//        StringBuilder sb = new StringBuilder();
//        sb.append("TwoVarLinearInequality{\n");
//
//        for (Identifier id : this.getKeys()) {
//            sb.append("  ").append(id).append(" -> {\n");
//            for (LinearInequality ineq : this.getState(id).elements) {
//                sb.append("    ").append(ineq).append("\n");
//            }
//            sb.append("  }\n");
//        }
//
//        sb.append("}");
//        String result = sb.toString();
//
//        return new StringRepresentation(result);
//
//

//------------------- Des fonctions pour l'affichage -------------------//
@Override
public StructuredRepresentation representation() {
    StringBuilder sb = new StringBuilder();
    sb.append("TwoVarLinearInequality{\n");
    sb.append("\n");

    Set<Identifier> userVariables = new HashSet<>();
    Set<Identifier> otherIdentifiers = new HashSet<>();

    for (Identifier id : this.getKeys()) {
        String name = id.getName();
        if (!name.contains("@") && !name.contains("pp") && name.length() < 10) {
            userVariables.add(id);
        } else {
            otherIdentifiers.add(id);
        }
    }

    for (Identifier id : userVariables) {
        sb.append("  ").append(id.getName()).append(" -> {\n");

        Set<LinearInequality> relevantInequalities = new HashSet<>();
        for (LinearInequality ineq : this.getState(id).elements) {
            boolean var1IsUser = ineq.getVar1() == null || !ineq.getVar1().getName().contains("@");
            boolean var2IsUser = ineq.getVar2() == null || !ineq.getVar2().getName().contains("@");

            if (var1IsUser && var2IsUser) {
                relevantInequalities.add(ineq);
            }
        }

        for (LinearInequality ineq : relevantInequalities) {
            sb.append("    ").append(formatInequality(ineq)).append(",\n");
        }
        sb.append("\n");
        sb.append("  }\n");
    }

    /*
    if (!otherIdentifiers.isEmpty()) {
        sb.append("  --- Internal References ---\n");
        for (Identifier id : otherIdentifiers) {
            sb.append("  ").append(simplifyName(id.getName())).append(" -> {\n");
            for (LinearInequality ineq : this.getState(id).elements) {
                sb.append("    ").append(formatInequality(ineq)).append("\n");
            }
            sb.append("  }\n");
        }
    }
    */

    sb.append("}");
    String result = sb.toString();

    return new StringRepresentation(result);
}

    // simplify the name for internal references
    private String simplifyName(String name) {
        if (name.contains("@")) {
            if (name.contains("'")) {
                int fileStart = name.indexOf("'");
                int fileEnd = name.lastIndexOf("'");
                if (fileStart != -1 && fileEnd != -1 && fileEnd > fileStart) {
                    String file = name.substring(fileStart + 1, fileEnd);
                    String[] parts = name.substring(fileEnd + 1).split(":");
                    if (parts.length >= 3) {
                        return "ref@" + file.substring(file.lastIndexOf('/') + 1) +
                                ":" + parts[1] + ":" + parts[2];
                    }
                }
            }
            return "ref" + name.hashCode() % 1000;
        }
        return name;
    }

    // Normalise affichage des inégalités linéaires
    private String formatInequality(LinearInequality ineq) {
        StringBuilder formatted = new StringBuilder();

        boolean hasTerms = false;

        if (ineq.getVar1() != null && Math.abs(ineq.getCoeff1()) > 1e-10) {
            double coeff = ineq.getCoeff1();
            String varName = simplifyName(ineq.getVar1().getName());

            if (Math.abs(coeff - 1.0) < 1e-10) {
                formatted.append(varName);
            } else if (Math.abs(coeff + 1.0) < 1e-10) {
                formatted.append("-").append(varName);
            } else {
                formatted.append(formatCoefficient(coeff)).append(varName);
            }
            hasTerms = true;
        }

        if (ineq.getVar2() != null && Math.abs(ineq.getCoeff2()) > 1e-10) {
            double coeff = ineq.getCoeff2();
            String varName = simplifyName(ineq.getVar2().getName());

            if (hasTerms) {
                if (coeff > 0) {
                    formatted.append(" + ");
                    if (Math.abs(coeff - 1.0) >= 1e-10) {
                        formatted.append(formatCoefficient(coeff));
                    }
                } else {
                    formatted.append(" - ");
                    if (Math.abs(coeff + 1.0) >= 1e-10) {
                        formatted.append(formatCoefficient(Math.abs(coeff)));
                    }
                }
            } else {
                if (Math.abs(coeff - 1.0) < 1e-10) {
                    formatted.append(varName);
                } else if (Math.abs(coeff + 1.0) < 1e-10) {
                    formatted.append("-").append(varName);
                } else {
                    formatted.append(formatCoefficient(coeff)).append(varName);
                }
                hasTerms = true;
            }

            formatted.append(varName);
        }

        formatted.append(" ≤ ").append(formatConstant(ineq.getConstant()));

        return formatted.toString();
    }

    private String formatCoefficient(double coeff) {
        if (Math.abs(coeff - Math.round(coeff)) < 1e-10) {
            return String.valueOf(Math.round(coeff));
        } else {
            return String.format("%.2f", coeff);
        }
    }

    private String formatConstant(double constant) {
        if (Math.abs(constant - Math.round(constant)) < 1e-10) {
            return String.valueOf(Math.round(constant));
        } else {
            return String.format("%.2f", constant);
        }
    }
}
