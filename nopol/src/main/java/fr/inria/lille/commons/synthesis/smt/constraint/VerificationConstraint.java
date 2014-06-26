package fr.inria.lille.commons.synthesis.smt.constraint;

import static java.util.Arrays.asList;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.smtlib.IExpr;
import org.smtlib.IExpr.IDeclaration;

import fr.inria.lille.commons.synthesis.smt.SMTLib;
import fr.inria.lille.commons.synthesis.smt.locationVariables.IndexedLocationVariable;
import fr.inria.lille.commons.synthesis.smt.locationVariables.LocationVariable;
import fr.inria.lille.commons.synthesis.smt.locationVariables.LocationVariableContainer;

public class VerificationConstraint extends CompoundConstraint {

	public VerificationConstraint(SMTLib smtlib) {
		super("Verification", smtlib, Arrays.asList(new ConnectivityConstraint(smtlib), new LibraryConstraint(smtlib)));
	}

	@Override
	public List<LocationVariable<?>> usedLocationVariables(LocationVariableContainer locationVariableContainer) {
		return locationVariableContainer.copyOfAllLocationVariables();
	}

	@Override
	protected List<IExpr> invocationArguments(LocationVariableContainer locationVariableContainer) {
		List<IExpr> arguments = (List) collectSubexpressions((List) locationVariableContainer.copyOfInputsAndOutput());
		arguments.addAll(collectExpressions(locationVariableContainer.copyOfOperatorsParametersAndOutput()));
		return arguments;
	}
	
	@Override
	protected List<IDeclaration> parameters(LocationVariableContainer locationVariableContainer) {
		List<IDeclaration> parameters = declarationsFromSubexpressions(locationVariableContainer.copyOfInputsAndOutput());
		parameters.addAll(declarationsFromExpressions(locationVariableContainer.copyOfOperatorsParametersAndOutput()));
		return parameters;
	}

	@Override
	protected Collection<IExpr> definitionExpressions(LocationVariableContainer locationVariableContainer) {
		IExpr predicate = conjunctionOf(subconstraintInvocations(locationVariableContainer));
		List<IDeclaration> declarations = declarationsFromSubexpressions(locationVariableContainer.copyOfOperatorsAndParameters());
		if (declarations.isEmpty()) {
			return (List) asList(predicate); 
		}
		return (List) asList(smtlib().exists(declarations, predicate));
	}
	
	@Override
	public List<IExpr> instantiatedArguments(LocationVariableContainer container, Map<String, Object> values) {
		List<Object> actualValues = IndexedLocationVariable.extractWithObjectExpressions(values, (List) container.copyOfInputsAndOutput());
		List<IExpr> arguments = asSMTExpressions(actualValues);
		arguments.addAll(collectExpressions(container.copyOfOperatorsParametersAndOutput()));
		return arguments;
	}
}