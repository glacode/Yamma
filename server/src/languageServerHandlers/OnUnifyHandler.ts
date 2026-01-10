import path = require('path');
import { Connection, TextDocuments, TextEdit } from 'vscode-languageserver';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { GlobalState } from '../general/GlobalState';
import { ConfigurationManager, LabelsOrderInCompressedProof, ProofMode } from '../mm/ConfigurationManager';
import { MmParser } from '../mm/MmParser';
import { applyTextEdits } from '../mm/Utils';
import { MmpParser } from '../mmp/MmpParser';
import { MmpUnifier } from '../mmp/MmpUnifier';
import { MmpValidator } from '../mmp/MmpValidator';
import { OnDidChangeContentHandler } from './OnDidChangeContentHandler';
import { ILabelMapCreatorForCompressedProof, IMmpCompressedProofCreator, MmpCompressedProofCreatorFromPackedProof } from '../mmp/proofCompression/MmpCompressedProofCreator';

export interface UnifyAndValidateArgs {
	textDocumentUri: string,
	connection: Connection,
	documents: TextDocuments<TextDocument>,
	hasConfigurationCapability: boolean,
	maxNumberOfHypothesisDispositionsForStepDerivation: number,
	globalState: GlobalState,
	renumber: boolean,
	removeUnusedStatements: boolean
}

export interface IUnificationResult {
	textEdits: TextEdit[];
	mmpParser?: MmpParser
}

export class OnUnifyHandler {
	// params: DocumentFormattingParams;
	// documents: TextDocuments<TextDocument>;
	mmParser: MmParser;
	configurationManager: ConfigurationManager;
	maxNumberOfHypothesisDispositionsForStepDerivation: number;
	globalState: GlobalState;

	// constructor(params: DocumentFormattingParams, mmParser: MmParser,
	constructor(private textDocumentUri: string, mmParser: MmParser, private mmpParser: MmpParser,
		configurationManager: ConfigurationManager, maxNumberOfHypothesisDispositionsForStepDerivation: number,
		private renumber: boolean, private removeUnusedStatements: boolean, globalState: GlobalState) {
		// this.params = params;
		// this.documents = documents;
		this.mmParser = mmParser;
		this.configurationManager = configurationManager;
		this.maxNumberOfHypothesisDispositionsForStepDerivation = maxNumberOfHypothesisDispositionsForStepDerivation;
		this.globalState = globalState;
	}

	//#region unifyIfTheCase

	//#region unify

	//#region parseMmpFile

	//#region buildMmpCompressedProofCreator
	private buildMmpCompressedProofCreator(labelsOrderInCompressedProof: LabelsOrderInCompressedProof):
		IMmpCompressedProofCreator {
		const labelMapCreatorForCompressedProof: ILabelMapCreatorForCompressedProof =
			MmpCompressedProofCreatorFromPackedProof.getLabelMapCreatorForCompressedProof(
				labelsOrderInCompressedProof, 4, 79);
		const mmpCompressedProofCreator: MmpCompressedProofCreatorFromPackedProof
			= new MmpCompressedProofCreatorFromPackedProof(labelMapCreatorForCompressedProof);
		return mmpCompressedProofCreator;
	}
	//#endregion buildMmpCompressedProofCreator

	private parseMmpFile(proofMode: ProofMode, labelsOrderInCompressedProof: LabelsOrderInCompressedProof):
		TextEdit[] {
		// const mmpParser: MmpParser = new MmpParser(textDocument, mmParser)
		// const mmpUnifier: MmpUnifier =
		// 	new MmpUnifier(this.mmParser.labelToStatementMap, this.mmParser.outermostBlock,
		// 		this.mmParser.grammar, this.mmParser.workingVars, proofMode, GlobalState.lastMmpParser);
		//TODO manage case GlobalState.lastMmpParser == undefined (invoke unify only if it is not undefined)
		const expectedTheoremLabel: string = path.parse(this.textDocumentUri).name;
		const mmpCompressedProofCreator: IMmpCompressedProofCreator =
			this.buildMmpCompressedProofCreator(labelsOrderInCompressedProof);
		const mmpUnifier: MmpUnifier =
			// new MmpUnifier(this.mmpParser, proofMode, this.maxNumberOfHypothesisDispositionsForStepDerivation,
			// 	this.renumber, expectedTheoremLabel, undefined, undefined, mmpCompressedProofCreator);
			new MmpUnifier(
				{
					mmpParser: this.mmpParser,
					proofMode: proofMode,
					maxNumberOfHypothesisDispositionsForStepDerivation: this.maxNumberOfHypothesisDispositionsForStepDerivation,
					renumber: this.renumber,
					removeUnusedStatements: this.removeUnusedStatements,
					expectedTheoremLabel: expectedTheoremLabel,
					mmpCompressedProofCreator: mmpCompressedProofCreator,
					globalState: this.globalState
				});
		// const textToParse: string = textDocument.getText();
		if (this.mmParser.grammar != undefined)
			mmpUnifier.unify();
		return mmpUnifier.textEditArray;
	}
	//#endregion parseMmpFile

	private async unify(): Promise<TextEdit[]> {
		// const proofMode: ProofMode = await this.configurationManager.proofMode(this.params.textDocument.uri);
		const proofMode: ProofMode = await this.configurationManager.proofMode(this.textDocumentUri);
		const labelsOrderInCompressedProof: LabelsOrderInCompressedProof =
			await this.configurationManager.labelsOrderInCompressedProof(this.textDocumentUri);
		const textEditArray: TextEdit[] = this.parseMmpFile(proofMode, labelsOrderInCompressedProof);
		return Promise.resolve(textEditArray);
	}
	//#endregion unify

	// static async unifyIfTheCase(textDocumentUri: string, documents: TextDocuments<TextDocument>,
	// 	globalState: GlobalState, maxNumberOfHypothesisDispositionsForStepDerivation: number,
	// 	// renumber: boolean): Promise<TextEdit[]> {
	// 	renumber: boolean): Promise<IUnificationResult> {
	static async unifyIfTheCase(unifyAndValidateArgs: UnifyAndValidateArgs): Promise<IUnificationResult> {
		// let result: Promise<TextEdit[]> = Promise.resolve([]);
		let result: Promise<IUnificationResult> = Promise.resolve({ textEdits: [] });
		if (unifyAndValidateArgs.globalState.mmParser != undefined &&
			unifyAndValidateArgs.globalState.lastMmpParser != undefined &&
			unifyAndValidateArgs.globalState.configurationManager != undefined) {
			const mmpParser: MmpParser | undefined = MmpValidator.buildMmpParserFromUri(
				unifyAndValidateArgs.textDocumentUri,
				unifyAndValidateArgs.documents,
				unifyAndValidateArgs.globalState.configurationManager.globalSettings.disjVarAutomaticGeneration,
				unifyAndValidateArgs.globalState.mmParser,
				unifyAndValidateArgs.globalState.formulaToParseNodeCache);
			if (mmpParser != undefined) {
				const onDocumentFormattingHandler: OnUnifyHandler =
					new OnUnifyHandler(
						unifyAndValidateArgs.textDocumentUri,
						unifyAndValidateArgs.globalState.mmParser,
						mmpParser,
						unifyAndValidateArgs.globalState.configurationManager,
						unifyAndValidateArgs.maxNumberOfHypothesisDispositionsForStepDerivation,
						unifyAndValidateArgs.renumber,
						unifyAndValidateArgs.removeUnusedStatements,
						unifyAndValidateArgs.globalState);
				const textEditArray: TextEdit[] = await onDocumentFormattingHandler.unify();
				const unificationResult: IUnificationResult = {
					mmpParser: mmpParser,
					textEdits: textEditArray
				};
				result = Promise.resolve(unificationResult);
				unifyAndValidateArgs.globalState.requireCursorPositionUpdate();
			}
		}
		return result;
		//#endregion unifyIfTheCase
	}


	//#region unifyAndValidate
	// private static async unifyIfTheCase(textDocumentUri: string): Promise<TextEdit[]> {
	// 	const result: Promise<TextEdit[]> = OnUnifyHandler.unifyIfTheCase(textDocumentUri,
	// 		globalState, Parameters.maxNumberOfHypothesisDispositionsForStepDerivation);
	// 	return result;
	// }

	//#region applyTextEditsAndValidate
	private static async requireValidation(textDocumentUri: string, connection: Connection,
		documents: TextDocuments<TextDocument>, hasConfigurationCapability: boolean,
		hasDiagnosticRelatedInformationCapability: boolean, globalState: GlobalState) {
		const textDocument: TextDocument = documents.get(textDocumentUri)!;
		if (textDocument != undefined)
			// this happens if unification is (mistakenly) required from a .mmt file
			await OnDidChangeContentHandler.validateTextDocument(textDocument,
				connection, hasConfigurationCapability, hasDiagnosticRelatedInformationCapability, globalState);
	}
	private static async applyTextEditsAndValidate(textEdits: TextEdit[], textDocumentUri: string,
		connection: Connection, documents: TextDocuments<TextDocument>,
		hasConfigurationCapability: boolean,
		globalState: GlobalState) {
		await applyTextEdits(textEdits, textDocumentUri, connection);
		// we require validation explicity, because sometimes applyEdit doesn't trigger a new validation,
		// at least in VSCode (for instance, if the applied change is equal to the previous text);
		// but we want a new validation, because it moves the cursor to the proper position
		await OnUnifyHandler.requireValidation(textDocumentUri, connection, documents, hasConfigurationCapability,
			hasConfigurationCapability, globalState);
	}
	//#endregion applyTextEditsAndValidate
	// static async unifyAndValidate(textDocumentUri: string, connection: Connection, documents: TextDocuments<TextDocument>,
	// 	hasConfigurationCapability: boolean, maxNumberOfHypothesisDispositionsForStepDerivation: number,
	// 	globalState: GlobalState, renumber: boolean): Promise<IUnificationResult> {
	// 	const result: IUnificationResult = await OnUnifyHandler.unifyIfTheCase(textDocumentUri, documents,
	// 		globalState, maxNumberOfHypothesisDispositionsForStepDerivation, renumber);
	// 	await OnUnifyHandler.applyTextEditsAndValidate(result.textEdits, textDocumentUri, connection, documents,
	// 		hasConfigurationCapability, globalState);
	// 	return result;
	// }
	static async unifyAndValidate(unifyAndValidateParams: UnifyAndValidateArgs): Promise<IUnificationResult> {
		const result: IUnificationResult = await OnUnifyHandler.unifyIfTheCase(
			unifyAndValidateParams);
		await OnUnifyHandler.applyTextEditsAndValidate(
			result.textEdits,
			unifyAndValidateParams.textDocumentUri,
			unifyAndValidateParams.connection,
			unifyAndValidateParams.documents,
			unifyAndValidateParams.hasConfigurationCapability,
			unifyAndValidateParams.globalState);
		return result;
	}
	//#endregion unifyAndValidate

}