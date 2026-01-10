import { Diagnostic, DiagnosticSeverity, TextDocuments } from 'vscode-languageserver';
import { Range, TextDocument } from 'vscode-languageserver-textdocument';
import { MmParser } from '../mm/MmParser';
import { IMmpParserParams, MmpParser, MmpParserErrorCode, MmpParserWarningCode } from './MmpParser';
import { AssertionStatement } from "../mm/AssertionStatement";
import { WorkingVars } from './WorkingVars';
import { GlobalState } from '../general/GlobalState';
import { MmpStatistics } from './MmpStatistics';
import { consoleLogWithTimestamp } from '../mm/Utils';
import { FormulaToParseNodeCache } from './FormulaToParseNodeCache';
import { IDiagnosticMessageForSyntaxError, ShortDiagnosticMessageForSyntaxError, VerboseDiagnosticMessageForSyntaxError } from './DiagnosticMessageForSyntaxError';
import DiagnosticMessageForSyntaxError, { DisjVarAutomaticGeneration } from '../mm/ConfigurationManager';
import { WorkingVarReplacerForCompleteProof } from './WorkingVarReplacerForCompleteProof';

/** validates a .mmp files and returns diagnostics
 * for the language server event handlers
 */
export class MmpValidator {
	mmParser: MmParser
	private formulaToParseNodeCache: FormulaToParseNodeCache;
	diagnostics: Diagnostic[] = [];
	mmpParser: MmpParser | undefined;

	constructor(mmParser: MmParser, private globalState: GlobalState,
		private diagnosticMessageForSyntaxError: DiagnosticMessageForSyntaxError) {
		this.mmParser = mmParser;
		this.formulaToParseNodeCache = globalState.formulaToParseNodeCache;
	}

	//#region validateFullDocument


	hypStack(assertionStatement: AssertionStatement): string[][] {
		const stack: string[][] = [];
		assertionStatement.frame?.fHyps.forEach(fHyp => {
			stack.push(fHyp.formula);
		});
		assertionStatement.frame?.eHyps.forEach(eHyp => {
			stack.push(eHyp.formula);
		});
		return stack;
	}

	//#region validateFullDocumentText
	private async updateStatistics(mmpParser: MmpParser) {
		const mmpStatistics: MmpStatistics = new MmpStatistics(mmpParser);
		mmpStatistics.buildStatistics();
		this.globalState.mmpStatistics = mmpStatistics;
	}

	// validateFullDocumentText(textToValidate: string, labelToStatementMap: Map<string, LabeledStatement>,
	// 	outermostBlock: BlockStatement, grammar: Grammar, workingVars: WorkingVars) {
	validateFullDocumentText(textToValidate: string, textDocumentUri: string,
		mmParser: MmParser, workingVars: WorkingVars) {
		// const mmpParser: MmpParser = new MmpParser(textToValidate, mmParser, workingVars,
		const diagnosticMessageForSyntaxError: IDiagnosticMessageForSyntaxError =
			(this.diagnosticMessageForSyntaxError == DiagnosticMessageForSyntaxError.verbose) ?
				new VerboseDiagnosticMessageForSyntaxError() : new ShortDiagnosticMessageForSyntaxError(
					mmParser.outermostBlock.c, mmParser.outermostBlock.v, 30);
		const mmpParserParams: IMmpParserParams = {
			textToParse: textToValidate,
			mmParser: mmParser,
			disjVarAutomaticGeneration: this.globalState.configurationManager?.globalSettings.disjVarAutomaticGeneration,
			workingVars: workingVars,
			formulaToParseNodeCache: this.formulaToParseNodeCache,
			diagnosticMessageForSyntaxError: diagnosticMessageForSyntaxError,
			documentUri: textDocumentUri
		};
		this.mmpParser = new MmpParser(mmpParserParams);
		// this.mmpParser = new MmpParser(textToValidate, mmParser, workingVars,
		// 	this.formulaToParseNodeCache, diagnosticMessageForSyntaxError, textDocumentUri);
		console.log('before mmpParser.parse()');
		this.mmpParser.parse();
		console.log('after mmpParser.parse()');
		this.globalState.lastMmpParser = this.mmpParser;
		this.diagnostics = this.mmpParser.diagnostics;

		if (this.globalState.isProofCompleteAndItContainsWorkingVarsAndThereAreNoUnusedTheoryVars) {
			const workingVarReplacerForCompleteProof: WorkingVarReplacerForCompleteProof =
				new WorkingVarReplacerForCompleteProof(this.mmpParser.mmpProof!);
			workingVarReplacerForCompleteProof.addDiagnosticsForMissingUnusedVars(this.diagnostics);
		}

		this.updateStatistics(this.mmpParser);
	}
	//#endregionvalidateFullDocumentText

	validateFullDocument(textDocument: TextDocument): Diagnostic[] {
		this.diagnostics = [];
		console.log('validateFullDocument - this.mmParser:' + this.mmParser);
		if (this.mmParser != undefined && this.mmParser.isParsingComplete) {
			// the parser has analyzed all the main .mm
			const textToValidate: string = textDocument.getText();
			if (this.mmParser.grammar != undefined)
				// mmpUnifier.unify(textToParse, mmParser.grammar);
				// this.validateFullDocumentText(textToValidate,
				// 	this.mmParser.labelToStatementMap, this.mmParser.outermostBlock,
				// 	this.mmParser.grammar, this.mmParser.workingVars);
				this.validateFullDocumentText(textToValidate, textDocument.uri,
					this.mmParser, this.mmParser.workingVars);
		}
		// const mmpUnifier = new MmpUnifier(this.mmParser.labelToStatementMap, this.mmParser.outermostBlock);
		// const textToParse: string = textDocument.getText();
		// if (this.mmParser.grammar != undefined)
		// 	mmpUnifier.unify(textToParse, this.mmParser.grammar);
		return this.diagnostics;
	}
	//#endregion validateFullDocument

	static addDiagnosticError(message: string, range: Range, code: MmpParserErrorCode, diagnostics: Diagnostic[]) {
		if (range.start.line < 0 || range.start.character < 0 || range.end.line < 0 || range.end.character < 0) {
			consoleLogWithTimestamp("diagnostic error NEGATIVE!!!");
			let forBreakPoint = 0; forBreakPoint = forBreakPoint + 1;
		}
		const diagnostic: Diagnostic = {
			severity: DiagnosticSeverity.Error,
			message: message,
			range: range,
			code: code,
			source: 'yamma'
		};
		diagnostics.push(diagnostic);
	}

	static addDiagnosticWarning(message: string, range: Range, code: MmpParserWarningCode, diagnostics: Diagnostic[]) {
		if (range.start.line < 0 || range.start.character < 0 || range.end.line < 0 || range.end.character < 0) {
			consoleLogWithTimestamp("diagnostic warning NEGATIVE!!!");
			let forBreakPoint = 0; forBreakPoint = forBreakPoint + 1;
		}
		const diagnostic: Diagnostic = {
			severity: DiagnosticSeverity.Warning,
			message: message,
			range: range,
			code: code,
			source: 'yamma'
		};
		diagnostics.push(diagnostic);
	}

	//#region buildMmpParserFromUri
	static buildMmpParserFromText(textToParse: string, disjVarAutomaticGeneration: DisjVarAutomaticGeneration,
		mmParser: MmParser, formulaToParseNodeCache: FormulaToParseNodeCache): MmpParser {
		const mmpParserParams: IMmpParserParams = {
			textToParse: textToParse,
			disjVarAutomaticGeneration: disjVarAutomaticGeneration,
			mmParser: mmParser,
			workingVars: mmParser.workingVars,
			formulaToParseNodeCache: formulaToParseNodeCache,
		};
		const mmpParser = new MmpParser(mmpParserParams);
		// const mmpParser = new MmpParser(textToParse, mmParser, mmParser.workingVars, formulaToParseNodeCache);
		mmpParser.parse();
		return mmpParser;
	}

	static buildMmpParserFromUri(textDocumentUri: string, documents: TextDocuments<TextDocument>,
		disjVarAutomaticGeneration: DisjVarAutomaticGeneration,
		mmParser: MmParser, formulaToParseNodeCache: FormulaToParseNodeCache): MmpParser | undefined {
		const textToParse: string | undefined = documents.get(textDocumentUri)?.getText();
		let mmpParser: MmpParser | undefined;
		if (textToParse != undefined) {
			mmpParser = MmpValidator.buildMmpParserFromText(
				textToParse, disjVarAutomaticGeneration, mmParser, formulaToParseNodeCache);
			return mmpParser;
		}
		//#endregion buildMmpParserFromUri
	}
}