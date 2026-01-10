import { Grammar, Parser } from 'nearley';
import { Diagnostic, Position, Range } from 'vscode-languageserver';
import { BlockStatement } from '../mm/BlockStatement';
import { MmLexer, MmToken } from '../grammar/MmLexer';
import { ProofStepFirstTokenInfo } from './MmpStatements';
import { MmpProofStep } from "./MmpProofStep";
import { MmpValidator } from './MmpValidator';
import { ProvableStatement } from "../mm/ProvableStatement";
import { LabeledStatement } from "../mm/LabeledStatement";
import { AssertionStatement } from "../mm/AssertionStatement";
import { range, oneCharacterRange, concatTokenValuesWithSpaces, concatWithSpaces, splitToTokensAllowingForEmptyValues, AreArrayTheSame, rebuildOriginalStringFromTokens } from '../mm/Utils';
import { WorkingVars } from './WorkingVars';
import { InternalNode, ParseNode } from '../grammar/ParseNode';
import { IMmpStatement, TextForProofStatement } from './MmpStatement';
import { MmpTheoremLabel } from "./MmpTheoremLabel";
import { MmpProof } from './MmpProof';
import { MmpSubstitutionBuilder, SubstitutionResult } from './MmpSubstitutionBuilder';
import { MmpSubstitutionApplier } from './MmpSubstitutionApplier';
import { GrammarManager } from '../grammar/GrammarManager';
import { OrderedPairOfNodes, UnificationAlgorithmState, WorkingVarsUnifierFinder } from './WorkingVarsUnifierFinder';
import { WorkingVarsUnifierInitializer } from './WorkingVarsUnifierInitializer';
import { DataFieldForMissingDjVarConstraintsDiagnostic, DisjointVarsManager } from '../mm/DisjointVarsManager';
import { MmLexerFromTokens } from '../grammar/MmLexerFromTokens';
import { TheoremCoherenceChecker } from '../mmt/TeoremCoherenceChecker';
import { MmpSearchStatement } from './MmpSearchStatement';
import { EHyp } from '../mm/EHyp';
import { MmParser } from '../mm/MmParser';
import { FormulaToParseNodeCache } from './FormulaToParseNodeCache';
import { Parameters } from '../general/Parameters';
import { IDiagnosticMessageForSyntaxError, ShortDiagnosticMessageForSyntaxError } from './DiagnosticMessageForSyntaxError';
import { MmpGetProofStatement } from './MmpGetProofStatement';
import { MmpAllowDiscouraged } from './MmpAllowDiscouraged';
import { MmpComment } from './MmpComment';
import { MmpDisjVarStatement } from './MmpDisjVarStatement';
import { DisjVarAutomaticGeneration } from '../mm/ConfigurationManager';






export enum MmpParserErrorCode {
	unexpectedEndOfFormula = "unexpectedEndOfFormula",
	formulaSyntaxError = "formulaSyntaxError",
	firstTokenWithMoreThanTwoColumns = "firstTokenWithMoreThanTwoColumns",
	stepRefCannotContainAComma = "stepRefCannotContainAComma",
	unknownLabel = "unknownLabel",
	provableStatementWithFailedVerification = "provableStatementWithFailedVerification",
	unificationError = "unificationError",
	workingVarUnificationError = "workingVarUnificationError",
	refStatementUnificationError = "refStatementUnificationError",
	wrongNumberOfEHyps = "wrongNumberOfEHyps",
	duplicatedEHyp = "duplicatedEHyp",
	wrongVariableKind = "wrongVariableKind",
	notAnAssertion = "notAnAssertion",
	unknownStepRef = "unknownStepRef",
	djVarsRestrictionViolated = "djVarsRestrictionViolated",
	disjVarSyntaxError = "disjVarSyntaxError",
	eHypLabelNotCoherentForAlreadyExistingTheorem = "eHypLabelNotCoherentForAlreadyExistingTheorem",
	missingQedStatementForAlreadyExistingTheorem = "missingQedStatementForAlreadyExistingTheorem",
	doesntMatchTheoryFormula = "doesntMatchTheoryFormula",
	disjVarConstraintNotInTheTheory = "disjVarConstraintNotInTheTheory",
	wrongNumberOfEHypsForAlreadyExistingTheorem = "wrongNumberOfEHypsForAlreadyExistingTheorem",
	disjVarWithItself = "disjVarWithItself",
	/** The formula in a $a or $e statement is not parsable wrt the grammar of the specific theory.
	The error is in the .mm file, not in the .mmp file, but we report it here also when we try to unify a proof step
	with a label for which the formula in the .mm is not parsable and the .mmp does not
	have a formula either, because the unifier is trying to create the unified formula,
	but the formula in the theory cannot have a parse node and so the unification fails */
	mmFormulaNonParsable = "FormulaNonParsable"
}




export enum MmpParserWarningCode {
	missingLabel = "missingLabel",
	missingFormula = "missingFormula",
	missingRef = "missingRef",
	missingEHyps = "missingEHyps",
	missingMandatoryDisjVarsStatement = "missingMandatoryDisjVarsStatement",
	missingDummyDisjVarsStatement = "missingDummyDisjVarsStatement",
	missingTheoremLabel = "missingTheoremLabel",
	lastStatementShouldBeQed = "lastStatementShouldBeQED",
	missingComment = "missingComment",
	isDiscouraged = "isDiscouraged",
	proofCompleteButWorkingVarsRemainAndNoUnusedTheoryVars = "proofCompleteButWorkingVarsRemainAndNoUnusedTheoryVars"
}


export interface IMmpParserParams {
	textToParse: string;
	mmParser: MmParser;
	workingVars: WorkingVars;
	disjVarAutomaticGeneration?: DisjVarAutomaticGeneration
	formulaToParseNodeCache?: FormulaToParseNodeCache;
	diagnosticMessageForSyntaxError?: IDiagnosticMessageForSyntaxError;
	documentUri?: string;
}

// Parser for .mmp files
export class MmpParser {

	textToParse: string;
	mmLexer: MmLexer;
	mmParser: MmParser;
	labelToStatementMap: Map<string, LabeledStatement>;
	outermostBlock: BlockStatement;
	grammar: Grammar;
	workingVars: WorkingVars;
	private diagnosticMessageForSyntaxError: IDiagnosticMessageForSyntaxError;
	/** when Parse() is invoked, it will contain the raw tokens produced by the MmLexer */
	mmTokens: MmToken[] | undefined;

	private _orderedPairsOfNodesForMGUalgorithm: OrderedPairOfNodes[];


	// static proofEHyps(mmpTokenizer: MmpTokenizer): EHyp[] {
	// 	throw new Error('Method not implemented.');
	// }
	// textDocument: TextDocument
	// mmParser: MmParser
	// mmpStatements: MmpStatement[] = []
	refToProofStepMap: Map<string, MmpProofStep>;  // maps each proof step id to the proof step

	allowDiscouraged = false; // true iff the $allowdiscouraged statement is present

	diagnostics: Diagnostic[] = [] // diagnostics built while parsing

	public disjVarAutomaticGeneration: DisjVarAutomaticGeneration;
	/** it will conatin the $d statements that are generated in place of warnings */
	disjVarStatementsAutomaticallyGenerated: MmpDisjVarStatement[] = [];

	mmpProof: MmpProof | undefined;

	/** the set of eHyp labels, for this theorem; used to check if there is an eHyp label
	 * duplication
	 */
	private eHypLabels: Set<string> = new Set<string>();
	public formulaToParseNodeCache: FormulaToParseNodeCache | undefined;
	public documentUri: string | undefined;

	//#region constructor
	// constructor(textToParse: string, labelToStatementMap: Map<string, LabeledStatement>,
	// 	outermostBlock: BlockStatement, grammar: Grammar, workingVars: WorkingVars) {
	constructor(public params: IMmpParserParams) {
		// this.textToParse = textToParse;
		// this.mmParser = mmParser;
		// this.labelToStatementMap = mmParser.labelToStatementMap;
		// this.outermostBlock = mmParser.outermostBlock;
		// this.grammar = mmParser.grammar;
		// this.workingVars = workingVars;

		// Handle the new interface case
		this.textToParse = this.params.textToParse;
		this.mmParser = params.mmParser;
		this.workingVars = params.workingVars;
		this.formulaToParseNodeCache = params.formulaToParseNodeCache;
		this.documentUri = params.documentUri;
		this.outermostBlock = this.mmParser.outermostBlock;
		this.diagnosticMessageForSyntaxError = (params.diagnosticMessageForSyntaxError != undefined) ?
			params.diagnosticMessageForSyntaxError : new ShortDiagnosticMessageForSyntaxError(
				this.outermostBlock.c, this.outermostBlock.v, 30);
		this.grammar = this.mmParser.grammar;
		this.labelToStatementMap = this.mmParser.labelToStatementMap;

		// if the automatic generation of disj var constraints is not specified, then it is set to GenerateNone
		// The Configuration default will probably be GenerateDummy, but we want this class to generate
		// all warnings, by default
		this.disjVarAutomaticGeneration = (params.disjVarAutomaticGeneration == undefined ?
			DisjVarAutomaticGeneration.GenerateNone : params.disjVarAutomaticGeneration);

		this.mmLexer = new MmLexer(this.workingVars);

		// this.mmParser = mmParser;
		this.refToProofStepMap = new Map<string, MmpProofStep>();
		// const textToParse: string = textDocument.getText();
		//this.createMmpStatements(textToParse);
		this._orderedPairsOfNodesForMGUalgorithm = [];


	}

	private addDiagnosticError(message: string, range: Range, code: MmpParserErrorCode) {
		MmpValidator.addDiagnosticError(message, range, code, this.diagnostics);
	}

	private addDiagnosticWarning(message: string, range: Range, code: MmpParserWarningCode) {
		MmpValidator.addDiagnosticWarning(message, range, code, this.diagnostics);
	}

	//#region  createProofSteps

	//#region createNextMmpStatement

	//#region createMmpStatementFromStepTokens

	//#region proofStepFirstTokenInfo
	static hypRefRanges(hypRefs: string[], currentRow: number, positions: number[]): Range[] {
		const hypRefRanges: Range[] = [];
		for (let i = 0; i < hypRefs.length; i++) {
			const hypRefRange: Range = range(hypRefs[i], currentRow, positions[i]);
			hypRefRanges.push(hypRefRange);
		}
		return hypRefRanges;
	}

	proofStepFirstTokenInfo(firstToken: MmToken): ProofStepFirstTokenInfo {
		const stringToParse = firstToken.value;

		// const firstTokenSplit = splitToTokens(firstToken.value, /[^:]+/g, firstToken.line, firstToken.column);
		// const stepLabel: MmToken | undefined = firstTokenSplit[firstTokenSplit.length - 1];
		let isEHyp = false;
		let stepRef: MmToken;
		// let hypRefs: MmToken[] = [];
		let hypRefs: MmToken[] | undefined;
		let stepLabel: MmToken | undefined;
		let unparsableToken: string | undefined;

		const firstColon: number = stringToParse.indexOf(":");
		if (firstColon === -1) {
			// there is no colon
			stepRef = new MmToken("", firstToken.line, firstToken.column);
			stepLabel = new MmToken(stringToParse, firstToken.line, firstToken.column);
		}
		else {
			// there is at least one colon
			// if (firstColon > 0) {
			// 	// the first colon is not the first character in the string to parse
			isEHyp = stringToParse.slice(0, firstColon).startsWith('h') ? true : false;
			const refIndexStart: number = isEHyp ? 1 : 0;
			stepRef = new MmToken(stringToParse.slice(refIndexStart, firstColon), firstToken.line, firstToken.column);
			if (stepRef.value.indexOf(",") != -1) {
				// the step ref contains a comm
				const message = "The ref cannot contain a comma";
				const range: Range = stepRef.range;
				const code = MmpParserErrorCode.stepRefCannotContainAComma;
				this.addDiagnosticError(message, range, code);
			}
			// }
			const secondColon: number = stringToParse.indexOf(":", firstColon + 1);
			if (secondColon === -1) {
				// there is only one colon
				if (firstColon < stringToParse.length - 1)
					// the only one colon is not the last character of the string to parse
					stepLabel = new MmToken(stringToParse.slice(firstColon + 1), firstToken.line, firstColon + 1);
			}
			else {
				// there are at least two colons
				const thirdColon: number = stringToParse.indexOf(":", secondColon + 1);
				if (thirdColon === -1) {
					// there are exactly two colons (the "standard" case)
					if (firstColon < secondColon) {
						// there is a nonempty substring between the first colon and the second colon
						const hypRefsSubstring: string = stringToParse.slice(firstColon + 1, secondColon);
						// hypRefs = splitToTokens(hypRefsSubstring, /[^,]+/g, firstToken.line, firstColon + 1);
						hypRefs = splitToTokensAllowingForEmptyValues(hypRefsSubstring, ",", firstToken.line, firstColon + 1);
					}
					if (secondColon < stringToParse.length - 1)
						// the second colon is not the last character of the string to parse
						stepLabel = new MmToken(stringToParse.slice(secondColon + 1), firstToken.line, secondColon + 1);
				} else {
					// there are more than two colons
					const message = "The first token can contain, at most, 2 colons";
					const range: Range = firstToken.range;
					const code = MmpParserErrorCode.firstTokenWithMoreThanTwoColumns;
					this.addDiagnosticError(message, range, code);
					unparsableToken = firstToken.value;
				}
			}
		}

		const firstTokenInfo: ProofStepFirstTokenInfo = new ProofStepFirstTokenInfo(
			firstToken, isEHyp, stepRef, hypRefs, stepLabel, unparsableToken);
		// , stepLabelRange: stepLabelRange
		return firstTokenInfo;
	}
	//#endregion proofStepFirstTokenInfo

	addTheoremLabel(nextProofStepTokens: MmToken[]) {
		let uTheoremLabel: MmpTheoremLabel | undefined;
		if (nextProofStepTokens.length == 1) {
			// the theorem label is missing
			const message = `The theorem label is missing`;
			const range: Range = oneCharacterRange(nextProofStepTokens[0].range.end);
			MmpValidator.addDiagnosticWarning(message, range,
				MmpParserWarningCode.missingTheoremLabel, this.diagnostics);
			uTheoremLabel = new MmpTheoremLabel(nextProofStepTokens[0]);
		} else
			// the second token is the theorem label
			uTheoremLabel = new MmpTheoremLabel(nextProofStepTokens[0], nextProofStepTokens[1]);
		this.mmpProof?.addMmpStatement(uTheoremLabel);
	}

	private addAllowDiscouraged(nextProofStepTokens: MmToken[]) {
		const allowDiscouraged = new MmpAllowDiscouraged(nextProofStepTokens[0]);
		this.mmpProof?.addMmpStatement(allowDiscouraged);
		this.allowDiscouraged = true;
	}

	addGetProofStatement(nextProofStepTokens: MmToken[]) {
		let mmpGetProofStatement: MmpGetProofStatement | undefined;
		if (nextProofStepTokens.length == 1) {
			// the theorem label is missing
			const message = `The theorem label is missing`;
			const range: Range = oneCharacterRange(nextProofStepTokens[0].range.end);
			MmpValidator.addDiagnosticWarning(message, range,
				MmpParserWarningCode.missingTheoremLabel, this.diagnostics);
			mmpGetProofStatement = new MmpGetProofStatement(nextProofStepTokens[0]);
		} else
			// the second token is the theorem label
			mmpGetProofStatement = new MmpGetProofStatement(nextProofStepTokens[0], nextProofStepTokens[1]);
		this.mmpProof?.addMmpStatement(mmpGetProofStatement);
	}

	//#region  addComment
	addDiagnosticForDefaultComment(comment: MmpComment) {
		if (comment.comment == Parameters.defaultComment) {
			// this is the default comment (automatically generated by yamma)
			const message = `This comment should contain a description of the theorem`;
			MmpValidator.addDiagnosticWarning(message, comment.contentTokens[1].range,
				MmpParserWarningCode.missingComment, this.diagnostics);
		}
	}
	addComment(nextProofStepTokens: MmToken[]) {
		// const commentContent: string = MmToken.joinValues(nextProofStepTokens.slice(1), " ");
		const commentContent: string = rebuildOriginalStringFromTokens(nextProofStepTokens);
		const comment: MmpComment = new MmpComment(nextProofStepTokens, commentContent);
		this.mmpProof?.addMmpStatement(comment);
		this.addDiagnosticForDefaultComment(comment);
	}
	//#endregion addComment

	addSearchStatement(searchStatementTokens: MmToken[]) {
		const mmpSearchStatement: MmpSearchStatement = new MmpSearchStatement(searchStatementTokens);
		this.mmpProof?.addMmpStatement(mmpSearchStatement);
	}

	addProofStep(proofStep: MmpProofStep) {
		this.mmpProof?.addMmpStep(proofStep);
		// this.mmpStatements.push(proofStep);
		if (proofStep.stepRefToken != undefined) {
			this.refToProofStepMap.set(proofStep.stepRefToken.value, proofStep);
		}
		// TODO handle case for proofStep.stepRef == undefined
	}

	//#region addDiagnosticForLabelAndEHypRefs
	private addDiagnosticMissingLabel(firstTokenEndPosition: Position) {
		const message = "Missing label";
		const range: Range = oneCharacterRange(firstTokenEndPosition);
		const code = MmpParserWarningCode.missingLabel;
		this.addDiagnosticWarning(message, range, code);
	}
	addDiagnisticsForEHypRefs(proofStepFirstTokenInfo: ProofStepFirstTokenInfo,
		stepLabel: MmToken, labeledStatement: AssertionStatement) {
		const refEHyps: number = proofStepFirstTokenInfo.eHypRefs == undefined ?
			0 : proofStepFirstTokenInfo.eHypRefs.length;
		if (proofStepFirstTokenInfo.stepRef.value != '' &&
			labeledStatement.frame?.eHyps.length != refEHyps) {
			const message = `Unification error: the assertion ${stepLabel.value} ` +
				`expects ${labeledStatement.frame?.eHyps.length} $e hypothesis, but ${refEHyps} are given`;
			const range: Range = proofStepFirstTokenInfo.eHypRefs == undefined ?
				stepLabel.range : <Range>proofStepFirstTokenInfo.eHypRefsRange;
			if (refEHyps == 0)
				// proofStep EHyps are either undefined or 0, but the logical assertion requires EHyps
				MmpValidator.addDiagnosticWarning(message, range, MmpParserWarningCode.missingEHyps,
					this.diagnostics);
			else
				// proofStep EHyps are defined, but their number does not match those of the logical assertion
				MmpValidator.addDiagnosticError(message, range, MmpParserErrorCode.wrongNumberOfEHyps,
					this.diagnostics);
		}
	}
	addDiagnosticForEHypLabel(stepLabel: MmToken) {
		// this is the label for an EHyp
		if (this.eHypLabels.has(stepLabel.value)) {
			const message = `This eHyp label is duplicated`;
			MmpValidator.addDiagnosticError(message, stepLabel.range,
				MmpParserErrorCode.duplicatedEHyp, this.diagnostics);
		}
		this.eHypLabels.add(stepLabel.value);
	}
	private addDiagnosticForLabelAndEHypRefs(firstTokenEndPosition: Position, proofStepFirstTokenInfo: ProofStepFirstTokenInfo) {
		if (proofStepFirstTokenInfo.stepLabel === undefined) {
			this.addDiagnosticMissingLabel(firstTokenEndPosition);
		} else if (proofStepFirstTokenInfo.isEHyp)
			this.addDiagnosticForEHypLabel(proofStepFirstTokenInfo.stepLabel);
		else {
			// current proof step is NOT an EHyp
			const stepLabel: MmToken = proofStepFirstTokenInfo.stepLabel;
			const labeledStatement: LabeledStatement | undefined =
				this.labelToStatementMap.get(stepLabel.value);
			if (labeledStatement == undefined) {
				const message = `Unknown label: this label does not exist in the logical system`;
				MmpValidator.addDiagnosticError(message, stepLabel.range,
					MmpParserErrorCode.unknownLabel, this.diagnostics);
			} else if (!(labeledStatement instanceof AssertionStatement)) {
				const message = `This is is not a label for an Assertion in the logical system`;
				MmpValidator.addDiagnosticError(message, stepLabel.range,
					MmpParserErrorCode.notAnAssertion, this.diagnostics);
			} else if (labeledStatement instanceof ProvableStatement &&
				labeledStatement.isProofVerificationFailed) {
				const message = `The verification of this statement failed. You can ` +
					`use $getproof to try to load its proof and fix it`;
				MmpValidator.addDiagnosticError(message, proofStepFirstTokenInfo.stepLabel.range,
					MmpParserErrorCode.provableStatementWithFailedVerification, this.diagnostics);
			} else if (labeledStatement.isDiscouraged && !this.allowDiscouraged) {
				const message = `The new use of '${stepLabel.value}' is discouraged.`;
				MmpValidator.addDiagnosticWarning(message, proofStepFirstTokenInfo.stepLabel.range,
					MmpParserWarningCode.isDiscouraged, this.diagnostics);
			}
			else if (!labeledStatement.parseNode) {
				const message = `\
The formula in the .mm file for '${stepLabel.value}' is not parsable. See the problem tab for the .mm file, for a detailed error message`;
				MmpValidator.addDiagnosticError(message, proofStepFirstTokenInfo.stepLabel.range,
					MmpParserErrorCode.mmFormulaNonParsable, this.diagnostics);
			}

			else {
				// labeledStatement instanceof AssertionStatement
				this.addDiagnisticsForEHypRefs(proofStepFirstTokenInfo,
					proofStepFirstTokenInfo.stepLabel, labeledStatement);
			}

		}
	}
	//#endregion addDiagnosticForLabelAndEHypRefs

	//#region getParseNode
	private static tryToParse(stepFormulaString: string, stepFormula: MmToken[], grammar: Grammar,
		workingVars: WorkingVars, diagnostics: Diagnostic[],
		diagnosticMessageForSyntaxError: IDiagnosticMessageForSyntaxError): InternalNode | undefined {
		let parseNode: InternalNode | undefined;
		// grammar.lexer = new MmLexer(workingVars);
		grammar.lexer = new MmLexerFromTokens(stepFormula);
		let parser: Parser = new Parser(grammar);
		// const stepFormulaString = concatTokenValuesWithSpaces(stepFormula);
		try {
			// parser.feed(stepFormulaString);
			// here we don't need to pass the actual formula string, because we use MmLexerFromTokens
			// that returns the original tokens of the formula
			parser.feed("");
			if (parser.results.length === 0) {
				// the formula was parsed till the end and no error was found, but at the end it
				// was not a valid formula
				// const stepFormulaString = concatTokenValuesWithSpaces(stepFormula);
				grammar.lexer = new MmLexer(workingVars);
				parser = new Parser(grammar);
				parser.feed(stepFormulaString + " UnxpexcteEndOfFormula");
			}
			if (parser.results.length > 1)
				throw new Error("Some ambiguity, let's look into it");
			parseNode = parser.results[0];
		} catch (error: any) {
			let range: Range = oneCharacterRange(stepFormula[stepFormula.length - 1].range.end);
			let errorCode: MmpParserErrorCode = MmpParserErrorCode.unexpectedEndOfFormula;
			if (parser.current < stepFormula.length) {
				// the parsing error was NOT for an and UnxpexcteEndOfFormula
				range = stepFormula[parser.current].range;
				errorCode = MmpParserErrorCode.formulaSyntaxError;
			}
			const diagnosticMessage: string = diagnosticMessageForSyntaxError.diagnosticMessage(<string>error.message);
			MmpValidator.addDiagnosticError(diagnosticMessage, range, errorCode, diagnostics);
		}
		return parseNode;
	}
	getParseNode(stepFormula: MmToken[]): InternalNode | undefined {
		const stepFormulaString: string = concatTokenValuesWithSpaces(stepFormula);
		let parseNode: InternalNode | undefined =
			this.formulaToParseNodeCache?.formulaToInternalNodeMap.get(stepFormulaString);
		if (parseNode == undefined) {
			parseNode = MmpParser.tryToParse(stepFormulaString, stepFormula, this.grammar,
				this.workingVars, this.diagnostics, this.diagnosticMessageForSyntaxError);
			if (parseNode != undefined && this.formulaToParseNodeCache != undefined
				&& !GrammarManager.containsWorkingVar(parseNode))
				this.formulaToParseNodeCache.add(stepFormulaString, parseNode);
		}
		return parseNode;
	}
	//#endregion getParseNode

	//#region getEHypMmpSteps
	private getEHypMmpStep(eHypRef: MmToken): (MmpProofStep | undefined) {
		let eHypStep: (MmpProofStep | undefined);
		if (eHypRef instanceof MmToken) {
			eHypStep = this.refToProofStepMap.get(eHypRef.value);
		}
		return eHypStep;
	}
	private getEHypMmpSteps(eHypRefs: MmToken[] | undefined, unknownStepRefs: Set<string>):
		(MmpProofStep | undefined)[] {
		const eHypMmpSteps: (MmpProofStep | undefined)[] = [];
		if (eHypRefs != undefined)
			eHypRefs.forEach((eHypRef: MmToken) => {
				if (eHypRef.value == "") {
					const message = `Missing reference`;
					MmpValidator.addDiagnosticWarning(message, eHypRef.range, MmpParserWarningCode.missingRef,
						this.diagnostics);
				}
				const eHypStep: (MmpProofStep | undefined) = this.getEHypMmpStep(eHypRef);
				if (eHypRef.value != "" && eHypStep == undefined) {
					const message = `This is not a reference for an existing proof step`;
					MmpValidator.addDiagnosticError(message, eHypRef.range, MmpParserErrorCode.unknownStepRef, this.diagnostics);
					unknownStepRefs.add(eHypRef.value);
				}
				eHypMmpSteps.push(eHypStep);
			});
		return eHypMmpSteps;
	}
	//#endregion getEHypMmpSteps

	//#region addDisjointVarConstraint
	addDiagnosticForExpectedVariable(mmToken: MmToken) {
		const errorMessage = `This is not a variable. A $d statement expects two variables`;
		MmpValidator.addDiagnosticError(errorMessage, mmToken.range, MmpParserErrorCode.disjVarSyntaxError, this.diagnostics);
	}
	addDisjointVarConstraint(nextProofStepTokens: MmToken[]) {
		if (nextProofStepTokens.length != 3) {
			const errorMessage = `After a $d , exactly 2 symbols are expected. We got ${nextProofStepTokens.length - 1} symbol/s instead.`;
			MmpValidator.addDiagnosticError(errorMessage, nextProofStepTokens[0].range, MmpParserErrorCode.disjVarSyntaxError, this.diagnostics);
		} else if (!this.outermostBlock.v.has(nextProofStepTokens[1].value))
			// the second symbol is NOT a variable
			this.addDiagnosticForExpectedVariable(nextProofStepTokens[1]);
		else if (!this.outermostBlock.v.has(nextProofStepTokens[2].value))
			// the third symbol is NOT a variable
			this.addDiagnosticForExpectedVariable(nextProofStepTokens[2]);
		else if (nextProofStepTokens[1].value == nextProofStepTokens[2].value) {
			// the two distinct variables are the same
			const errorMessage = `The two distinct variables are both '${nextProofStepTokens[1].value}' : ` +
				`a variable cannot be declared distinct from itself, the two symbols after a $d must be different.`;
			MmpValidator.addDiagnosticError(errorMessage, nextProofStepTokens[0].range, MmpParserErrorCode.disjVarWithItself, this.diagnostics);
		}
		else
			// there are exactly 2 distinctvariables, after the $d symbol
			// this.uProof?.addDisjointVarStatement(nextProofStepTokens[1].value, nextProofStepTokens[2].value);
			this.mmpProof?.addDisjointVarStatement(nextProofStepTokens);
	}
	//#endregion addDisjointVarConstraint

	createMmpProofStep(nextProofStepTokens: MmToken[]) {
		const proofStepFirstTokenInfo: ProofStepFirstTokenInfo =
			this.proofStepFirstTokenInfo(nextProofStepTokens[0]);
		if (proofStepFirstTokenInfo.unparsableToken === undefined)
			// the first token was at least parsable
			this.addDiagnosticForLabelAndEHypRefs(nextProofStepTokens[0].range.end,
				proofStepFirstTokenInfo);

		let stepFormula: MmToken[] | undefined;
		let formulaParseNode: InternalNode | undefined;
		if (nextProofStepTokens.length > 1) {
			// the step formula is present
			stepFormula = nextProofStepTokens.slice(1);
			formulaParseNode = this.getParseNode(stepFormula);
			// formulaParseNode = MmpParser.tryToParse(stepFormula, this.grammar, this.workingVars, this.diagnostics);
		}
		else {
			// missing formula
			const message = "Missing Formula";
			// the range for the diagnostic is one character after the first token
			const range: Range = oneCharacterRange({
				// line: nextProofStepTokens[0].line,
				// character: nextProofStepTokens[0].column + 1
				line: proofStepFirstTokenInfo.firstToken.range.start.line,
				character: proofStepFirstTokenInfo.firstToken.range.end.character
			});
			const code = MmpParserWarningCode.missingFormula;
			this.addDiagnosticWarning(message, range, code);
		}
		const unknownStepRefs: Set<string> = new Set<string>();
		const eHypMmpSteps: (MmpProofStep | undefined)[] =
			this.getEHypMmpSteps(proofStepFirstTokenInfo.eHypRefs, unknownStepRefs);
		const isFirstTokenParsable: boolean = proofStepFirstTokenInfo.unparsableToken == undefined;
		const proofStep: MmpProofStep = new MmpProofStep(this.mmpProof!, proofStepFirstTokenInfo,
			isFirstTokenParsable, proofStepFirstTokenInfo.isEHyp, proofStepFirstTokenInfo.stepRef,
			proofStepFirstTokenInfo.eHypRefs, eHypMmpSteps, proofStepFirstTokenInfo.stepLabel, stepFormula, formulaParseNode);
		if (unknownStepRefs.size > 0)
			// there was at least a step ref pointing to a non existent proof step
			proofStep.containsUnknownStepRef = true;
		this.addProofStep(proofStep);
	}
	addTextProofStatement(nextProofStepTokens: MmToken[]) {
		const textProofStatement: TextForProofStatement = new TextForProofStatement(nextProofStepTokens);
		this.mmpProof?.addMmpStatement(textProofStatement);
		this.mmpProof!.textProofStatement = textProofStatement;
	}
	createMmpStatementFromStepTokens(nextProofStepTokens: MmToken[]) {
		const nextTokenValue = nextProofStepTokens[0].value;
		if (nextTokenValue == "$theorem")
			this.addTheoremLabel(nextProofStepTokens);
		else if (nextTokenValue == "$allowdiscouraged")
			this.addAllowDiscouraged(nextProofStepTokens);
		else if (nextTokenValue == "$getproof")
			this.addGetProofStatement(nextProofStepTokens);
		else if (nextTokenValue.startsWith('*'))
			// currente statement is a comment
			this.addComment(nextProofStepTokens);
		else if (nextTokenValue == MmpSearchStatement.searchSymbolsKeyword)
			// current statement is a search statement
			this.addSearchStatement(nextProofStepTokens);
		else if (nextTokenValue.startsWith('$d'))
			// current statement is a disj var constraint
			this.addDisjointVarConstraint(nextProofStepTokens);
		else if (nextTokenValue == '$=')
			// current statement is a proof
			this.addTextProofStatement(nextProofStepTokens);
		else if (!nextTokenValue.startsWith('$'))
			// current statement is a proof step
			this.createMmpProofStep(nextProofStepTokens);
	}
	//#endregion createMmpStatementFromStepTokens

	private createNextMmpStatement(token: MmToken | undefined, mmLexer: MmLexer) {
		const nextProofStepTokens: MmToken[] = [];

		while (token != undefined && (nextProofStepTokens.length == 0 || token.column !== 0)) {
			nextProofStepTokens.push(token);
			token = mmLexer.next();
		}

		this.createMmpStatementFromStepTokens(nextProofStepTokens);
		return token;
	}
	//#endregion createNextMmpStatement

	//#region checkUnificationOfLogicalVars

	//#region checkUnificationWithUSubstitutionManager

	//#region  addDiagnisticsForSubstitution

	//#region addDiagnisticsForSubstitutionInEHyps
	addDiagnisticsForSubstitutionInEHyp(frameEHypParseNode: ParseNode, referencedEHypProofStep: MmpProofStep, range: Range,
		substitution: Map<string, InternalNode>) {

		// const expectedFormula: string[] =
		// MmpSubstitutionManager.applySubstitution(frameEHyp.formula, substitution);
		const expectedNode: ParseNode = MmpSubstitutionApplier.createParseNode(frameEHypParseNode,
			substitution, this.outermostBlock);
		const expectedFormula: string[] = GrammarManager.buildStringArray(expectedNode);
		const referencedFormula: MmToken[] | undefined = referencedEHypProofStep.stepFormula;
		if (referencedFormula != undefined) {
			const strArrReferencedFormula: string[] = MmToken.fromTokensToStrings(referencedFormula);
			if (!AreArrayTheSame(strArrReferencedFormula, expectedFormula)) {
				const strExpectedFormula = concatWithSpaces(expectedFormula);
				const strReferencedFormula = concatWithSpaces(strArrReferencedFormula);
				const message = `Unification error: referenced statement is '${strReferencedFormula}' but it was expected ` +
					`to be '${strExpectedFormula}'`;
				MmpValidator.addDiagnosticError(message, range,
					MmpParserErrorCode.refStatementUnificationError, this.diagnostics);
			}
		}
	}
	addDiagnisticsForSubstitutionInEHyps(frameEHyps: EHyp[], proofStep: MmpProofStep,
		substitution: Map<string, InternalNode>) {
		if (proofStep.eHypRefs != undefined && proofStep.eHypRefs.length == frameEHyps.length) {
			for (let i = 0; i < frameEHyps.length; i++) {
				const referencedEHypProofStep: MmpProofStep | undefined =
					<MmpProofStep | undefined>proofStep.eHypUSteps[i];
				// refToProofStepMap.get(proofStep.eHypRefs[i].value);
				if (referencedEHypProofStep != undefined && frameEHyps[i].parseNode != undefined)
					this.addDiagnisticsForSubstitutionInEHyp(
						frameEHyps[i].parseNode!, referencedEHypProofStep, proofStep.eHypRefs[i].range, substitution);
			}
		}
	}
	addDiagnisticsForAssertion(assertionStatementParseNode: ParseNode, proofStep: MmpProofStep,
		substitution: Map<string, InternalNode>) {
		const expectedNode = MmpSubstitutionApplier.createParseNode(
			assertionStatementParseNode, substitution, this.outermostBlock);
		// const expectedFormula: string[] =
		// 	MmpSubstitutionManager.applySubstitution(assertionStatement.formula, substitution);
		const expectedFormula: string[] = GrammarManager.buildStringArray(expectedNode);
		const proofStepFormula: MmToken[] | undefined = proofStep.stepFormula;
		if (proofStepFormula != undefined) {
			const strArrProofStepFormula: string[] = MmToken.fromTokensToStrings(proofStepFormula);
			if (!AreArrayTheSame(strArrProofStepFormula, expectedFormula)) {
				const strExpectedFormula = concatWithSpaces(expectedFormula);
				const strProofStepFormula = concatWithSpaces(strArrProofStepFormula);
				const message = `Unification error: statement is '${strProofStepFormula}' but it was expected ` +
					`to be '${strExpectedFormula}'`;
				MmpValidator.addDiagnosticError(message, (<MmToken>proofStep.stepLabelToken).range,
					MmpParserErrorCode.unificationError, this.diagnostics);
			}
		}
	}
	addDiagnisticsForSubstitution(frameEHyps: EHyp[], assertionStatement: AssertionStatement,
		proofStep: MmpProofStep, substitution: Map<string, InternalNode>) {
		if (assertionStatement.parseNode != undefined)
			this.addDiagnisticsForAssertion(assertionStatement.parseNode, proofStep, substitution);
		this.addDiagnisticsForSubstitutionInEHyps(frameEHyps, proofStep, substitution);
	}
	//#endregion addDiagnisticsForSubstitutionInEHyps

	//#endregion addDiagnisticsForSubstitution
	addStartingPairsForMGUFinder(mmpProofStep: MmpProofStep, assertion: AssertionStatement,
		substitution: Map<string, InternalNode>) {
		const workingVarsUnifierInitializer: WorkingVarsUnifierInitializer =
			new WorkingVarsUnifierInitializer(mmpProofStep, assertion, substitution, this.outermostBlock,
				this.grammar);
		const startingPairsForMGUAlgorthm: OrderedPairOfNodes[] =
			workingVarsUnifierInitializer.buildStartingPairsForMGUAlgorithm();
		this._orderedPairsOfNodesForMGUalgorithm =
			this._orderedPairsOfNodesForMGUalgorithm.concat(...startingPairsForMGUAlgorthm);
	}

	//#region checkDisjVarConstraints
	//#region addDiagnosticsOrGenerateDisjVarStatements
	isMissingDisjVar(diagnostic: Diagnostic): boolean {
		const result: boolean = (diagnostic.code == MmpParserWarningCode.missingDummyDisjVarsStatement
			|| diagnostic.code == MmpParserWarningCode.missingMandatoryDisjVarsStatement);
		return result;
	}
	isDiagnosticToBeAdded(diagnostic: Diagnostic) {
		let result = !this.isMissingDisjVar(diagnostic);
		if (!result) {
			// current diagnostic is for a missing $d statement
			const disjVarAutomaticGeneration: DisjVarAutomaticGeneration = this.disjVarAutomaticGeneration;
			result = (disjVarAutomaticGeneration == DisjVarAutomaticGeneration.GenerateNone ||
				(disjVarAutomaticGeneration == DisjVarAutomaticGeneration.GenerateDummy &&
					diagnostic.code == MmpParserWarningCode.missingMandatoryDisjVarsStatement)
			);
		}
		return result;
	}
	generateDisjVarStatement(dataFieldForMissingDjVarConstraintsDiagnostic: DataFieldForMissingDjVarConstraintsDiagnostic) {
		const disjVarStatement: MmpDisjVarStatement = MmpDisjVarStatement.CreateMmpDisjVarStatement(
			dataFieldForMissingDjVarConstraintsDiagnostic.missingDisjVar1,
			dataFieldForMissingDjVarConstraintsDiagnostic.missingDisjVar2);
		this.disjVarStatementsAutomaticallyGenerated.push(disjVarStatement);
	}
	addDiagnosticsOrGenerateDisjVarStatements(diagnostics: Diagnostic[]) {
		diagnostics.forEach((diagnostic: Diagnostic) => {
			if (this.isDiagnosticToBeAdded(diagnostic))
				this.diagnostics.push(diagnostic);
			else if (this.isMissingDisjVar(diagnostic))
				// if (this.isMissingDisjVar(diagnostic)) is not needed, because in the else branch it will always be true
				// But we add the check anyway, in the case the isDiagnosticToBeAdded() logic had to change
				this.generateDisjVarStatement(diagnostic.data as DataFieldForMissingDjVarConstraintsDiagnostic);
		});
	}
	//#endregion addDiagnosticsOrGenerateDisjVarStatements

	//TODO this method returns a single pair of Diagnostic for every DjVars constraint violation.
	// The reason is that we have a single substitution for every logical var: it is consistent,
	// thus, in principle, we could have multiple substitutions and then a Diagnostic for violating
	// var. Here's an explanatory example (see the corresponding test in DisjointVarsManager.test.ts):
	// qed:ax-5 |- ( y e. A -> A. y y e. A )
	// will return three constraint errors: one underlying ax-5, one underlying the first occurrence of
	// y (from the substitution of ph) and one underlying the second occurrence of y (from the substitution
	// of x). In principle, the third occurrence of y could also be underlined, because the second y e. A
	// is yet another substitution of ph.
	// You may consider adding all these diagnostics, in the future.
	protected checkDisjVarConstraints(assertion: AssertionStatement, substitution: Map<string, InternalNode>,
		stepLabelToken: MmToken, stepRef: string) {
		const disjointVarsManager: DisjointVarsManager =
			new DisjointVarsManager(assertion, substitution, this.outermostBlock,
				this.mmpProof!.mandatoryVars,
				true, stepLabelToken, stepRef, this.mmpProof);
		disjointVarsManager.checkDisjVarsConstraintsViolation();
		disjointVarsManager.checkMissingDisjVarsConstraints(<MmpProof>this.mmpProof);
		this.addDiagnosticsOrGenerateDisjVarStatements(disjointVarsManager.diagnostics);
		// this.diagnostics = this.diagnostics.concat(...disjointVarsManager.diagnostics);
	}
	//#endregion checkDisjVarConstraints

	checkUnificationWithUSubstitutionManager(mmpProofStep: MmpProofStep,
		outermostBlock: BlockStatement, grammar: Grammar, workingVars: WorkingVars) {
		if (mmpProofStep.stepLabel != undefined) {
			const stepLabelToken: MmToken = <MmToken>mmpProofStep.stepLabelToken;
			const labeledStatement: LabeledStatement | undefined =
				this.labelToStatementMap.get(stepLabelToken.value);
			if (labeledStatement instanceof AssertionStatement && !GrammarManager.isSyntaxAxiom2(labeledStatement)) {
				const uSubstitutionBuilder: MmpSubstitutionBuilder = new MmpSubstitutionBuilder(mmpProofStep,
					labeledStatement, outermostBlock, workingVars, grammar, this.diagnostics);
				const substitutionResult: SubstitutionResult = uSubstitutionBuilder.buildSubstitution();
				// const uSubstitutionBuilder: MmpSubstitutionBuilderNew = new MmpSubstitutionBuilderNew(mmpProofStep,
				// 	labeledStatement, outermostBlock, workingVars, grammar, this.diagnostics);
				// const substitutionResult: SubstitutionResult = uSubstitutionBuilder.buildSubstitution();
				if (!substitutionResult.hasBeenFound) {
					const substitution: Map<string, InternalNode> =
						uSubstitutionBuilder.buildACompleteSubstitutionEvenIfNonUnifiable();
					this.addDiagnisticsForSubstitution(labeledStatement.frame!.eHyps, labeledStatement,
						mmpProofStep, substitution);
				} else {
					// a valid substitution has been found
					const substitution: Map<string, InternalNode> =
						<Map<string, InternalNode>>substitutionResult.substitution;
					this.addStartingPairsForMGUFinder(mmpProofStep, labeledStatement, substitution);
					this.checkDisjVarConstraints(labeledStatement, substitution,
						mmpProofStep.stepLabelToken!, mmpProofStep.stepRef);
				}

			}
		}
	}
	//#endregion checkUnificationWithUSubstitutionManager

	/**
	 * Adds diagnostics for each unification in the proof
	 */
	checkUnificationOfLogicalVars(outermostBlock: BlockStatement,
		grammar: Grammar, workingVars: WorkingVars) {
		// this.mmpStatements.forEach((mmpStatement: MmpStatement) => {
		this.mmpProof?.mmpStatements.forEach((mmpStatement: IMmpStatement) => {
			// if (mmpStatement instanceof MmpProofStep && !mmpStatement.isEHyp) {
			if (mmpStatement instanceof MmpProofStep && !mmpStatement.isEHyp) {
				// const substitutionManager: MmpSubstitutionManager =
				// 	new MmpSubstitutionManager(labelToStatementMap, outermostBlock, this.diagnostics);
				// substitutionManager.checkUnificationForSingleMmpStep(mmpStatement, grammar, workingVars, this.refToProofStepMap);

				//tentativo nuovo con USubstitutionBuilder
				this.checkUnificationWithUSubstitutionManager(mmpStatement, outermostBlock, grammar, workingVars);
			}
		});
	}
	//#endregion checkUnificationOfLogicalVars


	/**
	 * parses the given text and builds the properties mmpStatements , refToProofStepMap and diagnostics;
	 * builds diagnostics, but it doesn't check for unification errors.
	 * This is mainly used for testing it separately from the whole method parse
	 * @param textToParse 
	 * @param labelToStatementMap  
	 * @param grammar 
	 */
	protected createMmpStatements() {
		// const mmLexer: MmLexer = new MmLexer(this.workingVars);
		const mmLexer: MmLexer = this.mmLexer;
		mmLexer.reset(this.textToParse);
		this.mmTokens = mmLexer.tokens;
		let token: MmToken | undefined = mmLexer.next();
		this.mmpProof = new MmpProof(this.outermostBlock, this.workingVars);
		while (token != undefined) {
			token = this.createNextMmpStatement(token, mmLexer);
			// token = mmLexer.current();
		}
	}

	checkQedStatement() {
		const lastMmpProofStep: MmpProofStep | undefined = this.mmpProof?.lastMmpProofStep;
		if (lastMmpProofStep != undefined && lastMmpProofStep.stepRef != 'qed') {
			const message = `The last proof step's ref is expected to be 'qed'`;
			const range: Range = lastMmpProofStep.stepRefToken.range;
			MmpValidator.addDiagnosticWarning(message, range,
				MmpParserWarningCode.lastStatementShouldBeQed, this.diagnostics);
		}
	}

	checkCoherenceIfAlreadyExistingTheorem() {
		const theoremName: string | undefined = this.mmpProof?.theoremLabel?.value;
		if (theoremName != undefined) {
			// the $theorem statement is present
			const labeledStatement: LabeledStatement | undefined = this.labelToStatementMap.get(theoremName);
			if (labeledStatement instanceof ProvableStatement) {
				// the current theorem is already in the theory
				const defaultRange: Range = this.mmpProof!.theoremLabel!.range;
				const theoremCoherenceChecker: TheoremCoherenceChecker = new TheoremCoherenceChecker(
					this.mmpProof!, labeledStatement, defaultRange, this.diagnostics);
				theoremCoherenceChecker.checkCoherence();
			}
		}
	}

	//#region checkUnificationOfWorkingVars

	//#region addDiagnosticsForWorkingVarsMGUerror
	//#region addDiagnosticForEachOccourenceOfWorkingVar
	addDiagnosticForOccourenceOfWorkingVarToSingleParseNode(parseNode: InternalNode, workingVar: string, errorMessage: string) {
		parseNode.parseNodes.forEach((childNode: ParseNode) => {
			if (childNode instanceof MmToken) {
				if (childNode.value == workingVar)
					MmpValidator.addDiagnosticError(errorMessage, childNode.range, MmpParserErrorCode.workingVarUnificationError,
						this.diagnostics);
			} else
				// parseNode instanceof InternalNode
				this.addDiagnosticForOccourenceOfWorkingVarToSingleParseNode(childNode, workingVar, errorMessage);

		});
	}
	addDiagnosticForOccourenceOfWorkingVarToSingleFormula(stepFormula: MmToken[], workingVar: string, errorMessage: string) {
		stepFormula.forEach((mmToken: MmToken) => {
			if (mmToken.value == workingVar)
				MmpValidator.addDiagnosticError(errorMessage, mmToken.range,
					MmpParserErrorCode.workingVarUnificationError, this.diagnostics);
		});
	}
	addDiagnosticForEachOccourenceOfWorkingVar(workingVar: string, errorMessage: string) {
		this.mmpProof?.mmpStatements.forEach((uStatement: IMmpStatement) => {
			// if (uStatement instanceof UProofStep && uStatement.parseNode != undefined) {
			// 	this.addDiagnosticForOccourenceOfWorkingVarToSingleParseNode(uStatement.parseNode,
			// 		workingVar, errorMessage);
			// }
			if (uStatement instanceof MmpProofStep && uStatement.stepFormula != undefined) {
				this.addDiagnosticForOccourenceOfWorkingVarToSingleFormula(uStatement.stepFormula,
					workingVar, errorMessage);
			}
		});
	}
	//#endregion addDiagnosticForEachOccourenceOfWorkingVar
	protected addDiagnosticsForWorkingVarsMGUerror(occourCheckOrderedPair: OrderedPairOfNodes) {
		const errorMessage: string = WorkingVarsUnifierFinder.buildErrorMessageForOccourCheckOrderedPair(
			occourCheckOrderedPair);
		const workingVar: string = GrammarManager.getTokenValueFromInternalNode(occourCheckOrderedPair.parseNode1);
		this.addDiagnosticForEachOccourenceOfWorkingVar(workingVar, errorMessage);
	}
	//#endregion addDiagnosticsForWorkingVarsMGUerror

	protected checkUnificationOfWorkingVars() {
		const workingVarsUnifierFinder: WorkingVarsUnifierFinder =
			new WorkingVarsUnifierFinder(this._orderedPairsOfNodesForMGUalgorithm);
		workingVarsUnifierFinder.findMostGeneralUnifier();
		if (workingVarsUnifierFinder.currentState == UnificationAlgorithmState.occourCheckFailure) {
			// the MGU algorithm stopped in error: a Working Var was required to be unified with a
			// node containing the Working Var itself

			this.addDiagnosticsForWorkingVarsMGUerror(
				<OrderedPairOfNodes>workingVarsUnifierFinder.occourCheckOrderedPair);
		}
	}
	//#endregion checkUnificationOfWorkingVars

	/**
	 * parses the given text and builds the properties mmpStatements , refToProofStepMap and diagnostics
	 * @param textToParse 
	 */
	parse() {
		// consoleLogWithTimestamp("Glauco_3: MmpParser.createProofSteps started");
		// TODO add diagnostics for mmParser.parseFailed == true
		// TODO add diagnostics for missing theorem name
		this.createMmpStatements();
		this.checkQedStatement();
		this.checkCoherenceIfAlreadyExistingTheorem();

		this.checkUnificationOfLogicalVars(this.outermostBlock, this.grammar, this.workingVars);
		this.checkUnificationOfWorkingVars();
		// consoleLogWithTimestamp("Glauco_5: MmpParser.createProofSteps end");
	}
	//#endregion createProofSteps

	//#endregion constructor
}
