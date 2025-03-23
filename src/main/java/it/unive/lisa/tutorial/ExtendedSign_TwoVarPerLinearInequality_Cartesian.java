package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;



public class ExtendedSign_TwoVarPerLinearInequality_Cartesian
        extends CartesianProduct<ExtendedSign_TwoVarPerLinearInequality_Cartesian, ValueEnvironment<ExtendedSignDomain>, TwoVarLinearInequality, ValueExpression, Identifier>
        implements ValueDomain<ExtendedSign_TwoVarPerLinearInequality_Cartesian> {


    public ExtendedSign_TwoVarPerLinearInequality_Cartesian() {
        this(new ValueEnvironment<>(new ExtendedSignDomain(ExtendedSignDomain.ExtendedSign.TOP)), new TwoVarLinearInequality());
    }

    public ExtendedSign_TwoVarPerLinearInequality_Cartesian(ValueEnvironment<ExtendedSignDomain> left, TwoVarLinearInequality right) {
        super(left, right);
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return left.knowsIdentifier(identifier) || right.knowsIdentifier(identifier);
    }

    @Override
    public ExtendedSign_TwoVarPerLinearInequality_Cartesian mk(
            ValueEnvironment<ExtendedSignDomain> left,
            TwoVarLinearInequality right) {
        return new ExtendedSign_TwoVarPerLinearInequality_Cartesian(left, right);
    }


    @Override
    public StructuredRepresentation representation() {
        if (isBottom() || isTop())
            return super.representation();

        StringBuilder sb = new StringBuilder();
        sb.append("ExtendedSign_TwoVarPerLinearInequality_Cartesian {\n");

        // afficher ExtendedSignDomain
        sb.append("  Global Sign Domain: ");
        sb.append(left.representation().toString());
        sb.append("\n\n");

        // afficher TwoVarLinearInequality
        sb.append("\n  Linear Inequalities:\n");
        String rightRepr = right.representation().toString();
        if (rightRepr.startsWith("TwoVarLinearInequality{")) {
            rightRepr = rightRepr.substring("TwoVarLinearInequality{".length(), rightRepr.length() - 1);
            rightRepr = rightRepr.replaceAll("\n", "\n  ");
            sb.append(rightRepr);
        } else {
            sb.append("  ").append(rightRepr);
        }

        sb.append("\n}");
        return new StringRepresentation(sb.toString());
    }
}
