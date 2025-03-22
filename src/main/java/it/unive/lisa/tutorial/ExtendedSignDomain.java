package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class ExtendedSignDomain implements BaseNonRelationalValueDomain<ExtendedSignDomain> {

    private final ExtendedSign sign;

    //constructor
    public ExtendedSignDomain(ExtendedSign extendedSign) {
        this.sign = extendedSign;
    }


    //we implement all the possible signs
    public enum ExtendedSign {
        BOTTOM,   // ⊥
        NEG,      // < 0
        ZERO,     // = 0
        POS,      // > 0
        NON_NEG,  // ≥ 0
        NON_POS,  // ≤ 0
        NON_ZERO, // ≠ 0
        TOP       // ⊤
    }

    public static final ExtendedSignDomain BOTTOM = new ExtendedSignDomain(ExtendedSign.BOTTOM);
    public static final ExtendedSignDomain ZERO = new ExtendedSignDomain(ExtendedSign.ZERO);
    public static final ExtendedSignDomain POS = new ExtendedSignDomain(ExtendedSign.POS);
    public static final ExtendedSignDomain NEG = new ExtendedSignDomain(ExtendedSign.NEG);
    public static final ExtendedSignDomain NON_NEG = new ExtendedSignDomain(ExtendedSign.NON_NEG);
    public static final ExtendedSignDomain NON_POS = new ExtendedSignDomain(ExtendedSign.NON_POS);
    public static final ExtendedSignDomain NON_ZERO = new ExtendedSignDomain(ExtendedSign.NON_ZERO);
    public static final ExtendedSignDomain TOP = new ExtendedSignDomain(ExtendedSign.TOP);


    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////                            Lattice                             ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    //-------------------------   Least upper bound   -------------------------------//
    @Override
    public ExtendedSignDomain lubAux(ExtendedSignDomain other) throws SemanticException {
        if (this.sign == ExtendedSign.BOTTOM)
            return other;
        if (other.sign == ExtendedSign.BOTTOM)
            return this;
        if (this.sign == ExtendedSign.TOP || other.sign == ExtendedSign.TOP)
            return TOP;

        // Hasse Graph
        // BOTTOM,   // ⊥
        // NEG,      // < 0
        // ZERO,     // = 0
        // POS,      // > 0
        // NON_NEG,  // ≥ 0
        // NON_POS,  // ≤ 0
        // NON_ZERO, // ≠ 0
        // TOP       // ⊤
        switch (this.sign) {
            case ZERO:
                switch (other.sign) {
                    case ZERO:
                        return ZERO;
                    case POS:
                        return NON_NEG;
                    case NEG:
                        return NON_POS;
                    case NON_NEG:
                        return NON_NEG;
                    case NON_POS:
                        return NON_POS;
                    case NON_ZERO:
                        return TOP;
                    default:
                        return TOP;
                }
            case POS:
                switch (other.sign) {
                    case ZERO:
                        return NON_NEG;
                    case POS:
                        return POS;
                    case NEG:
                        return NON_ZERO;
                    case NON_NEG:
                        return NON_NEG;
                    case NON_POS:
                        return TOP;
                    case NON_ZERO:
                        return NON_ZERO;
                    default:
                        return TOP;
                }
            case NEG:
                switch (other.sign) {
                    case ZERO:
                        return NON_POS;
                    case POS:
                        return NON_ZERO;
                    case NEG:
                        return NEG;
                    case NON_NEG:
                        return TOP;
                    case NON_POS:
                        return NON_POS;
                    case NON_ZERO:
                        return NON_ZERO;
                    default:
                        return TOP;
                }
            case NON_NEG:
                switch (other.sign) {
                    case ZERO:
                    case POS:
                    case NON_NEG:
                        return NON_NEG;
                    case NEG:
                    case NON_POS:
                    case NON_ZERO:
                        return TOP;
                    default:
                        return TOP;
                }
            case NON_POS:
                switch (other.sign) {
                    case ZERO:
                    case NEG:
                    case NON_POS:
                        return NON_POS;
                    case POS:
                    case NON_NEG:
                    case NON_ZERO:
                        return TOP;
                    default:
                        return TOP;
                }
            case NON_ZERO:
                switch (other.sign) {
                    case ZERO:
                        return TOP;
                    case POS:
                    case NEG:
                    case NON_ZERO:
                        return NON_ZERO;
                    case NON_NEG:
                    case NON_POS:
                        return TOP;
                    default:
                        return TOP;
                }
            default:
                return TOP;
        }
    }

    @Override
    public ExtendedSignDomain glbAux(ExtendedSignDomain other) throws SemanticException {
        if (this.sign == ExtendedSign.BOTTOM || other.sign == ExtendedSign.BOTTOM)
            return BOTTOM;

        // if any operand is TOP, the result is the other operand
        if (this.sign == ExtendedSign.TOP)
            return other;
        if (other.sign == ExtendedSign.TOP)
            return this;

        if (this.sign == other.sign)
            return this;

        // Hasse Graph
        switch (this.sign) {
            case ZERO:
                switch (other.sign) {
                    case POS:      return BOTTOM; // 0 ∧ >0 = ⊥
                    case NEG:      return BOTTOM; // 0 ∧ <0 = ⊥
                    case NON_NEG:  return ZERO;   // 0 ∧ ≥0 = 0
                    case NON_POS:  return ZERO;   // 0 ∧ ≤0 = 0
                    case NON_ZERO: return BOTTOM; // 0 ∧ ≠0 = ⊥
                    default:       return BOTTOM;
                }
            case POS:
                switch (other.sign) {
                    case ZERO:     return BOTTOM;   // >0 ∧ 0 = ⊥
                    case NEG:      return BOTTOM;   // >0 ∧ <0 = ⊥
                    case NON_NEG:  return POS;      // >0 ∧ ≥0 = >0
                    case NON_POS:  return BOTTOM;   // >0 ∧ ≤0 = ⊥
                    case NON_ZERO: return POS;      // >0 ∧ ≠0 = >0
                    default:       return BOTTOM;
                }
            case NEG:
                switch (other.sign) {
                    case ZERO:     return BOTTOM;   // <0 ∧ 0 = ⊥
                    case POS:      return BOTTOM;   // <0 ∧ >0 = ⊥
                    case NON_NEG:  return BOTTOM;   // <0 ∧ ≥0 = ⊥
                    case NON_POS:  return NEG;      // <0 ∧ ≤0 = <0
                    case NON_ZERO: return NEG;      // <0 ∧ ≠0 = <0
                    default:       return BOTTOM;
                }
            case NON_NEG:
                switch (other.sign) {
                    case ZERO:     return ZERO;     // ≥0 ∧ 0 = 0
                    case POS:      return POS;      // ≥0 ∧ >0 = >0
                    case NEG:      return BOTTOM;   // ≥0 ∧ <0 = ⊥
                    case NON_POS:  return ZERO;     // ≥0 ∧ ≤0 = 0
                    case NON_ZERO: return POS;      // ≥0 ∧ ≠0 = >0
                    default:       return BOTTOM;
                }
            case NON_POS:
                switch (other.sign) {
                    case ZERO:     return ZERO;     // ≤0 ∧ 0 = 0
                    case POS:      return BOTTOM;   // ≤0 ∧ >0 = ⊥
                    case NEG:      return NEG;      // ≤0 ∧ <0 = <0
                    case NON_NEG:  return ZERO;     // ≤0 ∧ ≥0 = 0
                    case NON_ZERO: return NEG;      // ≤0 ∧ ≠0 = <0
                    default:       return BOTTOM;
                }
            case NON_ZERO:
                switch (other.sign) {
                    case ZERO:     return BOTTOM;   // ≠0 ∧ 0 = ⊥
                    case POS:      return POS;      // ≠0 ∧ >0 = >0
                    case NEG:      return NEG;      // ≠0 ∧ <0 = <0
                    case NON_NEG:  return POS;      // ≠0 ∧ ≥0 = >0
                    case NON_POS:  return NEG;      // ≠0 ∧ ≤0 = <0
                    default:       return BOTTOM;
                }
            default:
                return BOTTOM;
        }
    }

    //-------------------------   ordre partiel   -------------------------------//
    @Override
    public boolean lessOrEqualAux(ExtendedSignDomain other) throws SemanticException {
        if (this.sign == other.sign)
            return true;
        if (this.sign == ExtendedSign.BOTTOM)
            return true;
        if (other.sign == ExtendedSign.TOP)
            return true;
        // Hasse Graph
        // BOTTOM,   // ⊥
        // NEG,      // < 0
        // ZERO,     // = 0
        // POS,      // > 0
        // NON_NEG,  // ≥ 0
        // NON_POS,  // ≤ 0
        // NON_ZERO, // ≠ 0
        // TOP       // ⊤
        switch (this.sign) {
            //= 0
            case ZERO:
                //≥ 0, ≤ 0
                return other.sign == ExtendedSign.NON_NEG ||
                        other.sign == ExtendedSign.NON_POS;
            //> 0
            case POS:
                //≤ 0, ≠ 0
                return other.sign == ExtendedSign.NON_NEG ||
                        other.sign == ExtendedSign.NON_ZERO;
            //< 0
            case NEG:
                //≤ 0, ≠ 0
                return other.sign == ExtendedSign.NON_POS ||
                        other.sign == ExtendedSign.NON_ZERO;
            case NON_NEG:
            case NON_POS:
            case NON_ZERO:
                return false;
            default:
                return false;
        }
    }

    //-------------------------   widening   -------------------------------//
    //here we use lubAux implementation as implementation of widening,because the lattice is finite
    @Override
    public ExtendedSignDomain wideningAux(ExtendedSignDomain other) throws SemanticException {
        return lubAux(other);
    }

    @Override
    public ExtendedSignDomain top() {
        return TOP;
    }

    @Override
    public ExtendedSignDomain bottom() {
        return BOTTOM;
    }

    @Override
    public StructuredRepresentation representation() {
        if (isBottom())
            return Lattice.bottomRepresentation();
        if (isTop())
            return Lattice.topRepresentation();

        String signStr;
        switch (sign) {
            case ZERO:
                signStr = "0";
                break;
            case POS:
                signStr = ">0";
                break;
            case NEG:
                signStr = "<0";
                break;
            case NON_NEG:
                signStr = "≥0";
                break;
            case NON_POS:
                signStr = "≤0";
                break;
            case NON_ZERO:
                signStr = "≠0";
                break;
            default:
                signStr = "?";
        }
        return new StringRepresentation(signStr);
    }

    ////////////////////////////////////////////////////////////////////////
    ////                                                                ////
    ////                          Semantique                            ////
    ////                                                                ////
    ////////////////////////////////////////////////////////////////////////
    @Override
    public ExtendedSignDomain evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Integer) {
            //recuperer le valeur et puis decider le signe
            int value = (Integer) constant.getValue();
            if (value == 0)
                return ZERO;
            if (value > 0)
                return POS;
            return NEG;
        }
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }

    //----------------------------- +,-,*,/ by definition dans l'article --------------------------//
    private ExtendedSignDomain add(ExtendedSignDomain left, ExtendedSignDomain right) {
        // if any operand is BOTTOM, the result is BOTTOM
        if (left.isBottom() || right.isBottom())
            return BOTTOM;
        // if any operand is TOP, the result is TOP (except if the other operand is BOTTOM)
        if (left.isTop() || right.isTop())
            return TOP;

        switch (left.sign) {
            case ZERO:
                switch (right.sign) {
                    case ZERO:     return ZERO;     // 0 + 0 = 0
                    case POS:      return POS;      // 0 + >0 = >0
                    case NEG:      return NEG;      // 0 + <0 = <0
                    case NON_NEG:  return NON_NEG;  // 0 + ≥0 = ≥0
                    case NON_POS:  return NON_POS;  // 0 + ≤0 = ≤0
                    case NON_ZERO: return NON_ZERO; // 0 + ≠0 = ≠0
                    default:       return TOP;
                }
            case POS:
                switch (right.sign) {
                    case ZERO:     return POS;      // >0 + 0 = >0
                    case POS:      return POS;      // >0 + >0 = >0
                    case NEG:      return TOP;      // >0 + <0 = T (could be any value)
                    case NON_NEG:  return POS;      // >0 + ≥0 = >0
                    case NON_POS:  return TOP;      // >0 + ≤0 = T
                    case NON_ZERO: return NON_ZERO; // >0 + ≠0 = ≠0
                    default:       return TOP;
                }
            case NEG:
                switch (right.sign) {
                    case ZERO:     return NEG;      // <0 + 0 = <0
                    case POS:      return TOP;      // <0 + >0 = T (could be any value)
                    case NEG:      return NEG;      // <0 + <0 = <0
                    case NON_NEG:  return TOP;      // <0 + ≥0 = T
                    case NON_POS:  return NEG;      // <0 + ≤0 = <0
                    case NON_ZERO: return NON_ZERO; // <0 + ≠0 = ≠0
                    default:       return TOP;
                }
            case NON_NEG:
                switch (right.sign) {
                    case ZERO:     return NON_NEG;  // ≥0 + 0 = ≥0
                    case POS:      return POS;      // ≥0 + >0 = >0
                    case NEG:      return TOP;      // ≥0 + <0 = T
                    case NON_NEG:  return NON_NEG;  // ≥0 + ≥0 = ≥0
                    case NON_POS:  return TOP;      // ≥0 + ≤0 = T
                    case NON_ZERO: return TOP;      // ≥0 + ≠0 = T
                    default:       return TOP;
                }
            case NON_POS:
                switch (right.sign) {
                    case ZERO:     return NON_POS;  // ≤0 + 0 = ≤0
                    case POS:      return TOP;      // ≤0 + >0 = T
                    case NEG:      return NEG;      // ≤0 + <0 = <0
                    case NON_NEG:  return TOP;      // ≤0 + ≥0 = T
                    case NON_POS:  return NON_POS;  // ≤0 + ≤0 = ≤0
                    case NON_ZERO: return TOP;      // ≤0 + ≠0 = T
                    default:       return TOP;
                }
            case NON_ZERO:
                switch (right.sign) {
                    case ZERO:     return NON_ZERO; // ≠0 + 0 = ≠0
                    case POS:      return NON_ZERO; // ≠0 + >0 = ≠0
                    case NEG:      return NON_ZERO; // ≠0 + <0 = ≠0
                    case NON_NEG:  return TOP;      // ≠0 + ≥0 = T
                    case NON_POS:  return TOP;      // ≠0 + ≤0 = T
                    case NON_ZERO: return NON_ZERO; // ≠0 + ≠0 = ≠0
                    default:       return TOP;
                }
            default:
                return TOP;
        }
    }
    private ExtendedSignDomain subtract(ExtendedSignDomain left, ExtendedSignDomain right) {
        // if any operand is BOTTOM, the result is BOTTOM
        if (left.isBottom() || right.isBottom())
            return BOTTOM;
        // if any operand is TOP, the result is TOP (except if the other operand is BOTTOM)
        if (left.isTop() || right.isTop())
            return TOP;

        switch (left.sign) {
            case ZERO:
                switch (right.sign) {
                    case ZERO:     return ZERO;     // 0 - 0 = 0
                    case POS:      return NEG;      // 0 - >0 = <0
                    case NEG:      return POS;      // 0 - <0 = >0
                    case NON_NEG:  return NON_POS;  // 0 - ≥0 = ≤0
                    case NON_POS:  return NON_NEG;  // 0 - ≤0 = ≥0
                    case NON_ZERO: return NON_ZERO; // 0 - ≠0 = ≠0
                    default:       return TOP;
                }
            case POS:
                switch (right.sign) {
                    case ZERO:     return POS;      // >0 - 0 = >0
                    case POS:      return TOP;      // >0 - >0 = T (could be any value)
                    case NEG:      return POS;      // >0 - <0 = >0
                    case NON_NEG:  return TOP;      // >0 - ≥0 = T
                    case NON_POS:  return POS;      // >0 - ≤0 = >0
                    case NON_ZERO: return TOP;      // >0 - ≠0 = T
                    default:       return TOP;
                }
            case NEG:
                switch (right.sign) {
                    case ZERO:     return NEG;      // <0 - 0 = <0
                    case POS:      return NEG;      // <0 - >0 = <0
                    case NEG:      return TOP;      // <0 - <0 = T
                    case NON_NEG:  return NEG;      // <0 - ≥0 = <0
                    case NON_POS:  return TOP;      // <0 - ≤0 = T
                    case NON_ZERO: return TOP;      // <0 - ≠0 = T
                    default:       return TOP;
                }
            case NON_NEG:
                switch (right.sign) {
                    case ZERO:     return NON_NEG;  // ≥0 - 0 = ≥0
                    case POS:      return TOP;      // ≥0 - >0 = T
                    case NEG:      return NON_NEG;  // ≥0 - <0 = ≥0
                    case NON_NEG:  return TOP;      // ≥0 - ≥0 = T
                    case NON_POS:  return NON_NEG;  // ≥0 - ≤0 = ≥0
                    case NON_ZERO: return TOP;      // ≥0 - ≠0 = T
                    default:       return TOP;
                }
            case NON_POS:
                switch (right.sign) {
                    case ZERO:     return NON_POS;  // ≤0 - 0 = ≤0
                    case POS:      return NEG;      // ≤0 - >0 = <0
                    case NEG:      return TOP;      // ≤0 - <0 = T
                    case NON_NEG:  return NON_POS;  // ≤0 - ≥0 = ≤0
                    case NON_POS:  return TOP;      // ≤0 - ≤0 = T
                    case NON_ZERO: return TOP;      // ≤0 - ≠0 = T
                    default:       return TOP;
                }
            case NON_ZERO:
                switch (right.sign) {
                    case ZERO:     return NON_ZERO; // ≠0 - 0 = ≠0
                    case POS:      return TOP;      // ≠0 - >0 = T
                    case NEG:      return TOP;      // ≠0 - <0 = T
                    case NON_NEG:  return TOP;      // ≠0 - ≥0 = T
                    case NON_POS:  return TOP;      // ≠0 - ≤0 = T
                    case NON_ZERO: return TOP;      // ≠0 - ≠0 = T
                    default:       return TOP;
                }
            default:
                return TOP;
        }
    }

    private ExtendedSignDomain multiply(ExtendedSignDomain left, ExtendedSignDomain right) {
        // if any operand is BOTTOM, the result is BOTTOM
        if (left.isBottom() || right.isBottom())
            return BOTTOM;
        // if any operand is ZERO, the result is ZERO (except if the other operand is BOTTOM)
        if (left.sign == ExtendedSign.ZERO || right.sign == ExtendedSign.ZERO)
            return ZERO;
        // if any operand is TOP, the result is TOP (except if the other operand is BOTTOM/ZERO)
        if (left.isTop() || right.isTop())
            return TOP;

        switch (left.sign) {
            case POS: // >0
                switch (right.sign) {
                    case POS:      return POS;      // >0 * >0 = >0
                    case NEG:      return NEG;      // >0 * <0 = <0
                    case NON_NEG:  return NON_NEG;  // >0 * ≥0 = ≥0
                    case NON_POS:  return NON_POS;  // >0 * ≤0 = ≤0
                    case NON_ZERO: return NON_ZERO; // >0 * ≠0 = ≠0
                    default:       return TOP;
                }
            case NEG: // <0
                switch (right.sign) {
                    case POS:      return NEG;      // <0 * >0 = <0
                    case NEG:      return POS;      // <0 * <0 = >0
                    case NON_NEG:  return NON_POS;  // <0 * ≥0 = ≤0
                    case NON_POS:  return NON_NEG;  // <0 * ≤0 = ≥0
                    case NON_ZERO: return NON_ZERO; // <0 * ≠0 = ≠0
                    default:       return TOP;
                }
            case NON_NEG: // ≥0
                switch (right.sign) {
                    case POS:      return NON_NEG;  // ≥0 * >0 = ≥0
                    case NEG:      return NON_POS;  // ≥0 * <0 = ≤0
                    case NON_NEG:  return NON_NEG;  // ≥0 * ≥0 = ≥0
                    case NON_POS:  return NON_POS;  // ≥0 * ≤0 = ≤0
                    case NON_ZERO: return TOP;      // ≥0 * ≠0 = T
                    default:       return TOP;
                }
            case NON_POS: // ≤0
                switch (right.sign) {
                    case POS:      return NON_POS;  // ≤0 * >0 = ≤0
                    case NEG:      return NON_NEG;  // ≤0 * <0 = ≥0
                    case NON_NEG:  return NON_POS;  // ≤0 * ≥0 = ≤0
                    case NON_POS:  return NON_NEG;  // ≤0 * ≤0 = ≥0
                    case NON_ZERO: return TOP;      // ≤0 * ≠0 = T
                    default:       return TOP;
                }
            case NON_ZERO: // ≠0
                switch (right.sign) {
                    case POS:      return NON_ZERO; // ≠0 * >0 = ≠0
                    case NEG:      return NON_ZERO; // ≠0 * <0 = ≠0
                    case NON_NEG:  return TOP;      // ≠0 * ≥0 = T
                    case NON_POS:  return TOP;      // ≠0 * ≤0 = T
                    case NON_ZERO: return NON_ZERO; // ≠0 * ≠0 = ≠0
                    default:       return TOP;
                }
            default:
                return TOP;
        }
    }

    private ExtendedSignDomain divide(ExtendedSignDomain left, ExtendedSignDomain right) {
        // if any operand is BOTTOM, the result is BOTTOM
        if (left.isBottom() || right.isBottom())
            return BOTTOM;

        // treatment of 0
        // division by 0 is BOTTOM
        if (right.sign == ExtendedSign.ZERO)
            return BOTTOM;

        // the result of 0/x is 0
        if (left.sign == ExtendedSign.ZERO)
            return ZERO;

        // if any operand is TOP, the result is TOP (except if the other operand is BOTTOM/ZERO)
        if (left.isTop() || right.isTop())
            return TOP;

        switch (left.sign) {
            case POS: // >0
                switch (right.sign) {
                    case POS:      return POS;      // >0 / >0 = >0
                    case NEG:      return NEG;      // >0 / <0 = <0
                    case NON_ZERO: return NON_ZERO; // >0 / ≠0 = ≠0
                    case NON_NEG:  return POS;      // >0 / ≥0 = >0
                    case NON_POS:  return NEG;      // >0 / ≤0 = <0
                    default:       return TOP;
                }
            case NEG: // <0
                switch (right.sign) {
                    case POS:      return NEG;      // <0 / >0 = <0
                    case NEG:      return POS;      // <0 / <0 = >0
                    case NON_ZERO: return NON_ZERO; // <0 / ≠0 = ≠0
                    case NON_NEG:  return NEG;      // <0 / ≥0 = <0
                    case NON_POS:  return POS;      // <0 / ≤0 = >0
                    default:       return TOP;
                }
            case NON_NEG: // ≥0
                switch (right.sign) {
                    case POS:      return NON_NEG;  // ≥0 / >0 = ≥0
                    case NEG:      return NON_POS;  // ≥0 / <0 = ≤0
                    case NON_ZERO: return TOP;      // ≥0 / ≠0 = T
                    case NON_NEG:  return NON_NEG;  // ≥0 / ≥0 = ≥0
                    case NON_POS:  return NON_POS;  // ≥0 / ≤0 = ≤0
                    default:       return TOP;
                }
            case NON_POS: // ≤0
                switch (right.sign) {
                    case POS:      return NON_POS;  // ≤0 / >0 = ≤0
                    case NEG:      return NON_NEG;  // ≤0 / <0 = ≥0
                    case NON_ZERO: return TOP;      // ≤0 / ≠0 = T
                    case NON_NEG:  return NON_POS;  // ≤0 / ≥0 = ≤0
                    case NON_POS:  return NON_NEG;  // ≤0 / ≤0 = ≥0
                    default:       return TOP;
                }
            case NON_ZERO: // ≠0
                switch (right.sign) {
                    case POS:      return NON_ZERO; // ≠0 / >0 = ≠0
                    case NEG:      return NON_ZERO; // ≠0 / <0 = ≠0
                    case NON_ZERO: return NON_ZERO; // ≠0 / ≠0 = ≠0
                    case NON_NEG:  return NON_ZERO; // ≠0 / ≥0 = ≠0
                    case NON_POS:  return NON_ZERO; // ≠0 / ≤0 = ≠0
                    default:       return TOP;
                }
            default:
                return TOP;
        }
    }

    @Override
    public ExtendedSignDomain evalBinaryExpression(BinaryOperator operator, ExtendedSignDomain left, ExtendedSignDomain right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isBottom() || right.isBottom())
            return bottom();

        // +
        if (operator instanceof AdditionOperator) {
            return add(left, right);
        }
        // -
        else if (operator instanceof SubtractionOperator) {
            return subtract(left, right);
        }
        // *
        else if (operator instanceof MultiplicationOperator) {
            return multiply(left, right);
        }
        // /
        else if (operator instanceof DivisionOperator) {
            return divide(left, right);
        }

        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public Satisfiability satisfiesBinaryExpression(BinaryOperator operator, ExtendedSignDomain left, ExtendedSignDomain right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isTop() || right.isTop())
            return Satisfiability.UNKNOWN;
        if (left.isBottom() || right.isBottom())
            return Satisfiability.UNKNOWN;

        // =
        if (operator instanceof ComparisonEq) {
            if (left.sign == ExtendedSign.POS && right.sign == ExtendedSign.NEG)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.NEG && right.sign == ExtendedSign.POS)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.NON_ZERO && right.sign == ExtendedSign.ZERO)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.ZERO && right.sign == ExtendedSign.NON_ZERO)
                return Satisfiability.NOT_SATISFIED;
            //only when we have 2 zero,we can say they are equal
            if (left.sign == ExtendedSign.ZERO && right.sign == ExtendedSign.ZERO)
                return Satisfiability.SATISFIED;

            return Satisfiability.UNKNOWN;
        }
        // !=
        else if (operator instanceof ComparisonNe) {
            // reverse the result of =
            Satisfiability eq = satisfiesBinaryExpression(ComparisonEq.INSTANCE, left, right, pp, oracle);
            return eq.negate();
        }
        // <
        else if (operator instanceof ComparisonLt) {
            if (left.sign == ExtendedSign.NEG && right.sign == ExtendedSign.POS)
                return Satisfiability.SATISFIED;
            if (left.sign == ExtendedSign.POS && right.sign == ExtendedSign.NEG)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.POS && right.sign == ExtendedSign.ZERO)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.ZERO && right.sign == ExtendedSign.NEG)
                return Satisfiability.NOT_SATISFIED;

            return Satisfiability.UNKNOWN;
        }
        // <=
        else if (operator instanceof ComparisonLe) {
            if (left.sign == ExtendedSign.NEG && right.sign == ExtendedSign.POS)
                return Satisfiability.SATISFIED;
            if (left.sign == ExtendedSign.POS && right.sign == ExtendedSign.NEG)
                return Satisfiability.NOT_SATISFIED;
            if (left.sign == ExtendedSign.ZERO && right.sign == ExtendedSign.ZERO)
                return Satisfiability.SATISFIED;

            return Satisfiability.UNKNOWN;
        }
        // >
        else if (operator instanceof ComparisonGt) {
            // a > b == b < a
            return satisfiesBinaryExpression(ComparisonLt.INSTANCE, right, left, pp, oracle);
        }
        // >=
        else if (operator instanceof ComparisonGe) {
            // a >= b == b <= a
            return satisfiesBinaryExpression(ComparisonLe.INSTANCE, right, left, pp, oracle);
        }

        return BaseNonRelationalValueDomain.super.satisfiesBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public ValueEnvironment<ExtendedSignDomain> assumeBinaryExpression(
            ValueEnvironment<ExtendedSignDomain> environment,
            BinaryOperator operator,
            ValueExpression left,
            ValueExpression right,
            ProgramPoint src,
            ProgramPoint dest,
            SemanticOracle oracle) throws SemanticException {

        if (left instanceof Variable) {
            Variable var = (Variable) left;
            ExtendedSignDomain rightEval = eval(right, environment, src, oracle);
            //var ? value
            return refineVariableByOperator(environment, var, operator, rightEval, true);
        }
        else if (right instanceof Variable) {
            Variable var = (Variable) right;
            ExtendedSignDomain leftEval = eval(left, environment, src, oracle);
            //value ? var
            return refineVariableByOperator(environment, var, operator, leftEval, false);
        }

        //we keep the same environment when it is not a variable
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }

    private ValueEnvironment<ExtendedSignDomain> refineVariableByOperator(
            ValueEnvironment<ExtendedSignDomain> environment,
            Variable var,
            BinaryOperator operator,
            ExtendedSignDomain value,
            boolean varIsLeft) throws SemanticException {

        // get the current state (sign) of the variable
        ExtendedSignDomain currentState = environment.getState(var);
        ExtendedSignDomain refinedState = null;

        // if bottom, the result is bottom
        if (currentState.isBottom() || value.isBottom())
            return environment.bottom();

        if (operator instanceof ComparisonEq) {
            // x == value: we take glb
            refinedState = currentState.glb(value);
        }
        else if (operator instanceof ComparisonNe) {
            // x != value: if value is zero, result is NON_ZERO
            if (value.sign == ExtendedSign.ZERO)
                refinedState = currentState.glb(NON_ZERO);
        }
        else if (operator instanceof ComparisonGt) {
            if (varIsLeft) {
                // x > value : x > 0
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(POS);
                // x > neg
                else if (value.sign == ExtendedSign.NEG)
                    refinedState = currentState.glb(NON_NEG);
            } else {
                // value > x
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NEG);
                else if (value.sign == ExtendedSign.POS)
                    refinedState = currentState.glb(NON_POS);
            }
        }
        else if (operator instanceof ComparisonGe) {
            if (varIsLeft) {
                // x >= value
                //x >= 0 -> non_neg
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NON_NEG);
                //x >= neg -> non_neg
                else if (value.sign == ExtendedSign.NEG)
                    refinedState = currentState.glb(NON_NEG);
            } else {
                // value >= x
                //inverse
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NON_POS);
                else if (value.sign == ExtendedSign.POS)
                    refinedState = currentState.glb(NON_POS);
            }
        }
        else if (operator instanceof ComparisonLt) {
            if (varIsLeft) {
                // x < value
                // x < 0 -> neg
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NEG);
                // x< pos -> non_pos
                else if (value.sign == ExtendedSign.POS)
                    refinedState = currentState.glb(NON_POS);
            } else {
                // value < x
                //inverse
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(POS);
                else if (value.sign == ExtendedSign.NEG)
                    refinedState = currentState.glb(NON_NEG);
            }
        }
        else if (operator instanceof ComparisonLe) {
            if (varIsLeft) {
                // x <= value
                //x <= 0 -> non_pos
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NON_POS);
                //x <= pos -> non_pos
                else if (value.sign == ExtendedSign.POS)
                    refinedState = currentState.glb(NON_POS);
            } else {
                // value <= x
                //inverse
                if (value.sign == ExtendedSign.ZERO)
                    refinedState = currentState.glb(NON_NEG);
                else if (value.sign == ExtendedSign.NEG)
                    refinedState = currentState.glb(NON_NEG);
            }
        }

        // if we cant refine the state, we keep the current state
        if (refinedState == null || refinedState.equals(currentState))
            return environment;

        if (refinedState.isBottom())
            return environment.bottom();

        // else update the state of the variable
        return environment.putState(var, refinedState);
    }



}
