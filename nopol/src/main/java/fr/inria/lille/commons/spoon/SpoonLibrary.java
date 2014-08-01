package fr.inria.lille.commons.spoon;

import static fr.inria.lille.commons.classes.ClassLibrary.castTo;
import static fr.inria.lille.commons.classes.ClassLibrary.isInstanceOf;

import java.io.File;
import java.util.Collection;
import java.util.List;

import spoon.Launcher;
import spoon.compiler.Environment;
import spoon.compiler.SpoonCompiler;
import spoon.reflect.code.BinaryOperatorKind;
import spoon.reflect.code.CtBinaryOperator;
import spoon.reflect.code.CtBlock;
import spoon.reflect.code.CtBreak;
import spoon.reflect.code.CtCodeElement;
import spoon.reflect.code.CtExpression;
import spoon.reflect.code.CtIf;
import spoon.reflect.code.CtLiteral;
import spoon.reflect.code.CtLocalVariable;
import spoon.reflect.code.CtNewClass;
import spoon.reflect.code.CtStatement;
import spoon.reflect.code.CtWhile;
import spoon.reflect.declaration.CtAnonymousExecutable;
import spoon.reflect.declaration.CtConstructor;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.declaration.CtField;
import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtModifiable;
import spoon.reflect.declaration.CtSimpleType;
import spoon.reflect.declaration.ModifierKind;
import spoon.reflect.factory.CodeFactory;
import spoon.reflect.factory.CoreFactory;
import spoon.reflect.factory.Factory;
import spoon.reflect.reference.CtTypeReference;
import spoon.reflect.visitor.Filter;
import spoon.reflect.visitor.Query;
import spoon.reflect.visitor.filter.TypeFilter;

import com.martiansoftware.jsap.JSAPException;

import fr.inria.lille.commons.collections.ListLibrary;
import fr.inria.lille.commons.collections.SetLibrary;

public class SpoonLibrary {
	
	public static Factory modelFor(File sourceFile) {
		Factory factory = newFactory();
		factory.getEnvironment().setDebug(true);
		try {
			SpoonCompiler compiler = launcher().createCompiler(factory);
			compiler.addInputSource(sourceFile);
			compiler.addTemplateSource(sourceFile);
			compiler.build();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return factory;
	}
	
	public static CtBlock<?> asBlock(CtStatement statement) {
		if (isBlock(statement)) {
			return (CtBlock<?>) statement;
		}
		return newBlock(statement.getFactory(), statement);
	}
	
	public static CtBreak newBreak(Factory factory) {
		return factory.Core().createBreak();
	}
	
	public static <T> CtLiteral<T> newLiteral(Factory factory, T value) {
		CtLiteral<T> newLiteral = factory.Core().createLiteral();
		newLiteral.setValue(value);
		return newLiteral;
	}
	
	public static <T> CtLocalVariable<T> newLocalVariableDeclaration(Factory factory, String classSimpleName, String variableName, T defaultValue, CtElement parent) {
		CtLocalVariable<T> localVariable = newLocalVariableDeclaration(factory, classSimpleName, variableName, defaultValue);
		setParent(parent, localVariable);
		return localVariable;
	}
	
	public static <T> CtLocalVariable<T> newLocalVariableDeclaration(Factory factory, String classSimpleName, String variableName, T defaultValue) {
		CtTypeReference<T> type = factory.Core().createTypeReference();
		type.setSimpleName(classSimpleName);
		CtLiteral<T> defaultExpression = newLiteral(factory, defaultValue);
		return factory.Code().createLocalVariable(type, variableName, defaultExpression);
	}

	public static <T> CtExpression<T> newExpressionFromSnippet(Factory factory, String codeSnippet, Class<T> expressionClass, CtElement parent) {
		CtExpression<T> expression = newExpressionFromSnippet(factory, codeSnippet, expressionClass);
		setParent(parent, expression);
		return expression;
	}
	
	public static <T> CtExpression<T> newExpressionFromSnippet(Factory factory, String codeSnippet, Class<T> expressionClass) {
		return factory.Code().createCodeSnippetExpression(codeSnippet);
	}
	
	public static CtStatement newStatementFromSnippet(Factory factory, String codeSnippet, CtElement parent) {
		CtStatement statement = newStatementFromSnippet(factory, codeSnippet);
		setParent(parent, statement);
		return statement;
	}
	
	public static CtStatement newStatementFromSnippet(Factory factory, String codeSnippet) {
		return factory.Code().createCodeSnippetStatement(codeSnippet);
	}

	public static CtBlock<CtStatement> newBlock(Factory factory, CtStatement... statements) {
		return newBlock(factory, ListLibrary.newArrayList(statements));
	}
	
	public static CtBlock<CtStatement> newBlock(Factory factory, List<CtStatement> blockStatements) {
		CtBlock<CtStatement> newBlock = factory.Core().createBlock();
		setParent(newBlock, blockStatements);
		newBlock.setStatements(blockStatements);
		return newBlock;
	}
	
	public static CtExpression<Boolean> newConjunctionExpression(Factory factory, CtExpression<Boolean> leftExpression, CtExpression<Boolean> rightExpression) {
		return newComposedExpression(factory, leftExpression, rightExpression, BinaryOperatorKind.AND);
	}
	
	public static <T> CtExpression<T> newComposedExpression(Factory factory, CtExpression<T> leftExpression, CtExpression<T> rightExpression, BinaryOperatorKind operator) {
		CtBinaryOperator<T> composedExpression = factory.Code().createBinaryOperator(leftExpression, rightExpression, operator);
		setParent(composedExpression, leftExpression, rightExpression);
		return composedExpression;
	}
	
	public static CtIf newIf(Factory factory, CtExpression<Boolean> condition, CtStatement thenBranch) {
		CtIf newIf = factory.Core().createIf();
		thenBranch = asBlock(thenBranch);
		setParent(newIf, condition, thenBranch);
		newIf.setCondition(condition);
		newIf.setThenStatement(thenBranch);
		return newIf;
	}
	
	public static CtIf newIf(Factory factory, CtExpression<Boolean> condition, CtStatement thenBranch, CtStatement elseBranch) {
		CtIf newIf = newIf(factory, condition, thenBranch);
		elseBranch = asBlock(elseBranch);
		setParent(newIf, elseBranch);
		newIf.setElseStatement(elseBranch);
		return newIf;
	}
	
	public static void setParent(CtElement parent, Collection<? extends CtElement> children) {
		setParent(parent, children.toArray(new CtElement[children.size()]));
	}
	
	public static void setParent(CtElement parent, CtElement... children) {
		for (CtElement child : children) {
			child.setParent(parent);
		}
	}
	
	public static void setLoopBody(CtWhile loop, CtStatement loopBody) {
		loopBody = asBlock(loopBody);
		setParent(loop, loopBody);
		loop.setBody(loopBody);
	}
	
	public static void setLoopingCondition(CtWhile loop, CtExpression<Boolean> loopingCondition) {
		setParent(loop, loopingCondition);
		loop.setLoopingExpression(loopingCondition);
	}
	
	public static <T extends CtElement> List<T> filteredElements(Factory factory, Filter<T> filter) {
		return Query.getElements(factory, filter);
	}
	
	public static <T extends CtElement> Collection<T> childrenWithParent(CtElement rootElement, Class<T> childrenClasses) {
		Collection<T> childrenWithParent = SetLibrary.newHashSet();
		Collection<T> allChildren = allChildrenOf(rootElement, childrenClasses);
		for (T child : allChildren) {
			if (child.getParent(rootElement.getClass()) == rootElement) {
				childrenWithParent.add(child);
			}
		}
		return childrenWithParent;
	}
	
	public static <T extends CtElement> Collection<T> allChildrenOf(CtElement rootElement, Class<T> childrenClasses) {
		return (Collection) Query.getElements(rootElement, new TypeFilter<>(childrenClasses));
	}
	
	public static boolean isBlock(CtElement element) {
		return isInstanceOf(CtBlock.class, element);
	}
	
	public static boolean isMethod(CtElement element) {
		return isInstanceOf(CtMethod.class, element);
	}
	
	public static boolean isLocalVariable(CtElement element) {
		return isInstanceOf(CtLocalVariable.class, element);
	}
	
	public static boolean isAnonymousClass(CtElement element) {
		return isInstanceOf(CtNewClass.class, element);
	}
	
	public static boolean isConstructor(CtElement element) {
		return isInstanceOf(CtConstructor.class, element);
	}
	
	public static boolean isInitializationBlock(CtElement element) {
		return isInstanceOf(CtAnonymousExecutable.class, element);
	}
	
	public static boolean isAType(CtElement element) {
		return isInstanceOf(CtSimpleType.class, element);
	}
	
	public static boolean isField(CtElement element) {
		return isInstanceOf(CtField.class, element);
	}
	
	public static boolean isStatement(CtElement element) {
		return isInstanceOf(CtStatement.class, element);
	}
	
	public static boolean isVoidType(CtTypeReference<?> type) {
		return type.getSimpleName().equalsIgnoreCase("void");
	}
	
	public static boolean allowsModifiers(CtElement element) {
		return isInstanceOf(CtModifiable.class, element);
	}
	
	public static boolean hasStaticModifier(CtElement element) {
		if (allowsModifiers(element)) {
			return castTo(CtModifiable.class, element).getModifiers().contains(ModifierKind.STATIC);
		}
		return false;
	}
	
	public static boolean inStaticCode(CtElement element) {
		if (allowsModifiers(element)) {
			return hasStaticModifier(element);
		}
		return hasStaticModifier(element.getParent(CtModifiable.class)) || hasStaticModifier(element.getParent(CtSimpleType.class));
	}
	
	public static boolean isLastStatementOfMethod(CtStatement statement) {
		CtElement statementParent = statement.getParent();
		if (! isBlock(statementParent)) {
			return isLastStatementOfMethod((CtStatement) statementParent);
		}
		CtBlock<?> block = (CtBlock<?>) statementParent;
		if (isLastStatementOf(block, statement)) {
			CtElement blockParent = block.getParent();
			if (isStatement(blockParent)) {
				return isLastStatementOfMethod((CtStatement) blockParent);
			} else {
				return isMethod(blockParent);
			}
		}
		return false;
	}
	
	public static boolean isLastStatementOf(CtBlock<?> block, CtStatement statement) {
		List<CtStatement> statements = block.getStatements();
		CtStatement lastStatement = ListLibrary.last(statements);
		return lastStatement == statement;
	}
	
	public static CtStatement statementOf(CtCodeElement codeElement) {
		Class<CtStatement> statementClass = CtStatement.class;
		if (isInstanceOf(statementClass, codeElement)) {
			return castTo(statementClass, codeElement);
		}
		return codeElement.getParent(statementClass);
	}
	
	public static CoreFactory coreFactoryOf(CtElement element) {
		return element.getFactory().Core();
	}
	
	public static CodeFactory codeFactoryOf(CtElement element) {
		return element.getFactory().Code();
	}
	
	public static Environment newEnvironment() {
		return newFactory().getEnvironment();
	}
	
	public static Factory newFactory() {
		return launcher().createFactory();
	}
	
	private static Launcher launcher() {
		if (launcher == null) {
			try {
				launcher = new Launcher();
			} catch (JSAPException e) {
				e.printStackTrace();
			}
		}
		return launcher;
	}
	
	private static Launcher launcher;
}
