package fr.inria.lille.commons.synthesis;

import java.util.Collection;
import java.util.Map;

import org.smtlib.ICommand;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr;
import org.smtlib.IExpr.ISymbol;

import fr.inria.lille.commons.collections.ListLibrary;
import fr.inria.lille.commons.synthesis.smt.SMTLib;
import fr.inria.lille.commons.synthesis.smt.constraint.CompoundConstraint;
import fr.inria.lille.commons.synthesis.smt.constraint.Constraint;
import fr.inria.lille.commons.synthesis.smt.constraint.VerificationConstraint;
import fr.inria.lille.commons.synthesis.smt.constraint.WellFormedProgramConstraint;
import fr.inria.lille.commons.synthesis.smt.locationVariables.LocationVariable;
import fr.inria.lille.commons.synthesis.smt.locationVariables.LocationVariableContainer;

public class SynthesisScriptBuilder {
	
	public SynthesisScriptBuilder() {
		this.smtlib = new SMTLib();
		wellFormedConstraint = new WellFormedProgramConstraint(smtlib());
		verificationConstraint = new VerificationConstraint(smtlib());
	}

	public SMTLib smtlib() {
		return smtlib;
	}
	
	public ISymbol smtLogic() {
		return SMTLib.logicAuflira();
	}
	
	public IScript scriptFrom(LocationVariableContainer container, Collection<Map<String,Object>> collectedValues) {
		Collection<ICommand> commands = commandsFrom(container);
		Collection<ICommand> assertions = assertionsFor(container, collectedValues);
		return smtlib().scriptFrom(smtLogic(), commands, assertions);
	}
	
	public Collection<ICommand> commandsFrom(LocationVariableContainer container) {
		Collection<ICommand> commands = ListLibrary.newLinkedList();
		addLocationVariableDeclarations(commands, container);
		addDefinitions(commands, wellFormedConstraint(), container);
		addDefinitions(commands, verificationConstraint(), container);
		return commands;
	}
	
	public Collection<ICommand> assertionsFor(LocationVariableContainer container, Collection<Map<String,Object>> collectedValues) {
		Collection<ICommand> assertions = ListLibrary.newLinkedList();
		addVerificationAssertions(assertions, container, collectedValues);
		assertions.add(smtlib().assertion(wellFormedConstraint().invocation(container)));
		return assertions;
	}
	
	private void addDefinitions(Collection<ICommand> commands, CompoundConstraint compoundConstraint, LocationVariableContainer container) {
		for (Constraint constraint : compoundConstraint.subconstraints()) {
			commands.add(constraint.definition(container));
		}
		commands.add(compoundConstraint.definition(container));
	}
	
	private void addLocationVariableDeclarations(Collection<ICommand> commands, LocationVariableContainer container) {
		for (LocationVariable<?> locationVariable : container.copyOfOperatorsParametersAndOutput()) {
			commands.add(smtlib().constant(locationVariable.expression(), SMTLib.intSort()));
		}
	}
	
	private void addVerificationAssertions(Collection<ICommand> assertions, LocationVariableContainer container, Collection<Map<String, Object>> collectedValues) {
		for (Map<String, Object> values : collectedValues) {
			IExpr invocation = verificationConstraint().invocationWithValues(container, values);
			assertions.add(smtlib().assertion(invocation));
		}
	}
	
	private CompoundConstraint wellFormedConstraint() {
		return wellFormedConstraint;
	}
	
	private CompoundConstraint verificationConstraint() {
		return verificationConstraint;		
	}
	
	private SMTLib smtlib;
	private CompoundConstraint wellFormedConstraint;
	private CompoundConstraint verificationConstraint;
}
