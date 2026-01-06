
import { GrammarManager } from '../grammar/GrammarManager';
import { MmToken } from '../grammar/MmLexer';
import { AssertionStatement } from '../mm/AssertionStatement';
import { BlockStatement } from '../mm/BlockStatement';
import { EHyp } from '../mm/EHyp';
import { FHyp } from '../mm/FHyp';
import { Frame } from '../mm/Frame';
import { LabeledStatement } from '../mm/LabeledStatement';
import { ProvableStatement } from '../mm/ProvableStatement';
import { Statement, ZIStatement, ZRStatement } from '../mm/Statements';
import { concatWithSpaces, fromStringsToTokens, rebuildOriginalStringFromTokens, splitToTokensDefault } from '../mm/Utils';
import { Verifier } from '../mm/Verifier';
import { MmpComment } from './MmpComment';
import { MmpProof } from './MmpProof';
import { MmpProofStep } from './MmpProofStep';
import { ProofStepFirstTokenInfo } from './MmpStatements';
import { MmpTheoremLabel } from './MmpTheoremLabel';
import { ProofCompressor } from './ProofCompressor';
import { WorkingVars } from './WorkingVars';

export class MmToMmpConverter {
	private mmpProof: MmpProof;
	private stack: string[][] = [];
	private stored: string[][] = [];
	private verifier: Verifier = new Verifier([]);
	private formulaStringToMmpProofStepMap: Map<string, MmpProofStep> = new Map<string, MmpProofStep>();

	constructor(private theoremLabel: string, private outermostBlock: BlockStatement,
		private labelToStatementMap: Map<string, LabeledStatement>) {
		//TODO you may use a parameter, instead of the hardcoded '1' below
		this.mmpProof = new MmpProof(this.outermostBlock, new WorkingVars(new Map<string, string>()), 1);
	}

	//#region buildProof

	//#region buildProofForProvableStatement
	addTheoremLabel(label: string) {
		const mmpTheoremLabel: MmpTheoremLabel = new MmpTheoremLabel(
			new MmToken("$theorem", 0, 0), new MmToken(label, 0, 0));
		this.mmpProof.addMmpStatement(mmpTheoremLabel);
	}
	addComment(comment: MmToken[]) {
		const commentContent: string = rebuildOriginalStringFromTokens(comment);
		const newComment: string = '* ' + commentContent.slice(2);
		const newTokens: MmToken[] = splitToTokensDefault(newComment);
		const mmpComment: MmpComment = new MmpComment(newTokens, newComment);
		this.mmpProof.addMmpStatement(mmpComment);
	}
	private addHeaderStatements(provableStatement: ProvableStatement) {
		this.addTheoremLabel(provableStatement.Label);
		if (provableStatement.comment != undefined && provableStatement.comment.length > 0)
			this.addComment(provableStatement.comment);
	}
	//#region addMmpStatements

	private isFormulaAlreadyInTheProof(formula: string[]): boolean {
		const textForFormula: string = concatWithSpaces(formula);
		const isAlreadyInThProof: boolean = (this.formulaStringToMmpProofStepMap.get(textForFormula)
			!= undefined);
		return isAlreadyInThProof;
	}

	getStepRef(isLastStatementInMmProof: boolean): string {
		// let stepRef = this.mmpProof.mmpStatements.length.toString();
		// removes the leading 'd' character
		let stepRef = this.mmpProof.getNewRef().substring(1);
		if (isLastStatementInMmProof)
			stepRef = 'qed';
		return stepRef;
	}

	//#region addEHypMmpProofSteps
	addEHypMmpProofStep(eHyp: EHyp) {
		const stepRef: string = this.getStepRef(false);
		const stepRefToken: MmToken = new MmToken(stepRef, 0, 0);
		const firstToken: MmToken = this.buildFirstToken(stepRef, [], eHyp.Label);
		const labelToken: MmToken = new MmToken(eHyp.Label, 0, 0);
		const firstTokenInfo: ProofStepFirstTokenInfo = new ProofStepFirstTokenInfo(
			firstToken, true, stepRefToken, [], labelToken);
		const formula: MmToken[] = fromStringsToTokens(eHyp.formula);
		const mmpProofStep: MmpProofStep = new MmpProofStep(this.mmpProof, firstTokenInfo, true, true,
			firstTokenInfo.stepRef, firstTokenInfo.eHypRefs, [], firstTokenInfo.stepLabel, formula);
		this.mmpProof.addMmpStep(mmpProofStep);
		this.formulaStringToMmpProofStepMap.set(mmpProofStep.textForFormula!, mmpProofStep);
	}
	addEHypMmpProofSteps(provableStatement: ProvableStatement) {
		provableStatement.frame?.eHyps.forEach((statement: Statement) => {
			if (statement instanceof EHyp && !this.isFormulaAlreadyInTheProof(statement.formula))
				this.addEHypMmpProofStep(statement);
		});
	}
	//#endregion addEHypMmpProofSteps



	//#region addSingleStepToMmpProof

	//#region addAssertionStatementWithSubstitution

	//#region buildMmpProofStep
	//#region getEHypMmpSteps
	//#region getEHypMmpStep
	getFormulaStringWithSubstitution(formula: string[], substitution: Map<string, string[]>): string {
		const formulaWithSubstitution: string[] =
			this.verifier.applySubstitution(formula, substitution);
		const formulaStringWithSubstitution: string = concatWithSpaces(formulaWithSubstitution);
		return formulaStringWithSubstitution;
	}
	getEHypMmpStep(eHyp: EHyp, substitution: Map<string, string[]>): MmpProofStep {
		const eHypFormulaStringWithSubstitution: string = this.getFormulaStringWithSubstitution(
			eHyp.formula, substitution);
		const mmpProofStep: MmpProofStep = this.formulaStringToMmpProofStepMap.get(
			eHypFormulaStringWithSubstitution)!;
		return mmpProofStep;
	}
	//#endregion getEHypMmpStep
	getEHypMmpSteps(assertionStatementProofStep: AssertionStatement,
		substitution: Map<string, string[]>):
		MmpProofStep[] {
		const eHypMmpSteps: MmpProofStep[] = [];
		assertionStatementProofStep.frame!.eHyps.forEach((eHyp: EHyp) => {
			const eHypMmpStep: MmpProofStep = this.getEHypMmpStep(eHyp, substitution);
			eHypMmpSteps.push(eHypMmpStep);
		});
		return eHypMmpSteps;
	}
	//#endregion getEHypMmpSteps

	//#region buildFirstTokenInfo
	//#region buildFirstToken
	getStepRefs(eHypMmpSteps: MmpProofStep[]): string {
		let stepRefs: string = eHypMmpSteps.length == 0 ? '' : eHypMmpSteps[0].stepRef;
		for (let i = 1; i < eHypMmpSteps.length; i++)
			stepRefs += ',' + eHypMmpSteps[i].stepRef;
		return stepRefs;
	}
	buildFirstToken(stepRef: string, eHypMmpSteps: MmpProofStep[],
		stepLabel: string): MmToken {
		const stepRefs: string = this.getStepRefs(eHypMmpSteps);
		// const firstTokenValue = stepRef + '::';
		const firstTokenValue = `${stepRef}:${stepRefs}:${stepLabel}`;
		const firstToken: MmToken = new MmToken(firstTokenValue, 0, 0);
		return firstToken;
	}
	//#endregion buildFirstToken
	buildEHypRefs(eHypMmpSteps: MmpProofStep[]): MmToken[] {
		const eHypRefs: MmToken[] = [];
		eHypMmpSteps.forEach((eHypMmpStep: MmpProofStep) => {
			const eHypRef: MmToken = new MmToken(eHypMmpStep.stepRef, 0, 0);
			eHypRefs.push(eHypRef);
		});
		return eHypRefs;
	}
	buildFirstTokenInfo(assertionStatementProofStep: AssertionStatement,
		eHypMmpSteps: MmpProofStep[],
		isLastStatementInMmProof: boolean): ProofStepFirstTokenInfo {
		const isEHyp = false;
		const stepRef: string = this.getStepRef(isLastStatementInMmProof);
		const stepRefToken: MmToken = new MmToken(stepRef, 0, 0);
		const firstToken: MmToken = this.buildFirstToken(stepRef, eHypMmpSteps,
			assertionStatementProofStep.Label);
		const eHypRefs: MmToken[] = this.buildEHypRefs(eHypMmpSteps);
		const labelToken: MmToken = new MmToken(assertionStatementProofStep.Label, 0, 0);
		const proofStepFirstTokenInfo: ProofStepFirstTokenInfo = new ProofStepFirstTokenInfo(
			firstToken, isEHyp, stepRefToken, eHypRefs, labelToken);
		return proofStepFirstTokenInfo;
	}
	//#endregion buildFirstTokenInfo

	buildMmpProofStep(assertionStatementProofStep: AssertionStatement,
		assertionStatementWithSubstitution: string[], substitution: Map<string, string[]>,
		isLastStatementInMmProof: boolean): MmpProofStep {
		const eHypMmpSteps: MmpProofStep[] = this.getEHypMmpSteps(
			assertionStatementProofStep, substitution);
		const firstTokenInfo: ProofStepFirstTokenInfo = this.buildFirstTokenInfo(
			assertionStatementProofStep, eHypMmpSteps, isLastStatementInMmProof);
		const formula: MmToken[] = fromStringsToTokens(assertionStatementWithSubstitution);
		const mmpProofStep: MmpProofStep = new MmpProofStep(this.mmpProof, firstTokenInfo, true, false,
			firstTokenInfo.stepRef, firstTokenInfo.eHypRefs, eHypMmpSteps,
			firstTokenInfo.stepLabel, formula);
		return mmpProofStep;
	}
	//#endregion buildMmpProofStep
	private addAssertionStatementWithSubstitution(assertionStatementProofStep: AssertionStatement,
		assertionStatementWithSubstitution: string[], substitution: Map<string, string[]>,
		isLastStatementInMmProof: boolean) {
		const mmpProofStep: MmpProofStep = this.buildMmpProofStep(assertionStatementProofStep,
			assertionStatementWithSubstitution, substitution, isLastStatementInMmProof);
		this.mmpProof.addMmpStep(mmpProofStep);
		this.formulaStringToMmpProofStepMap.set(mmpProofStep.textForFormula!
			, mmpProofStep);
	}
	//#endregion addAssertionStatementWithSubstitution
	private addSingleStepToMmpProof(assertionStatementProofStep: AssertionStatement,
		isLastStatementInMmProof: boolean) {
		const frameProofStep: Frame = <Frame>assertionStatementProofStep.frame;
		const popCount: number = frameProofStep.fHyps.length + frameProofStep.eHyps.length;
		const fHypsStack: string[][] = this.verifier.fHypsStack(frameProofStep, this.stack);
		const substitution: Map<string, string[]> =
			this.verifier.buildSubstitution(frameProofStep.fHyps, fHypsStack);
		for (let i = 0; i < popCount; i++)
			this.stack.pop();
		const assertionStatementWithSubstitution: string[] =
			this.verifier.applySubstitution(assertionStatementProofStep.formula, substitution);
		if (!GrammarManager.isSyntaxAxiom2(assertionStatementProofStep) &&
			!this.isFormulaAlreadyInTheProof(assertionStatementWithSubstitution))
			this.addAssertionStatementWithSubstitution(assertionStatementProofStep,
				assertionStatementWithSubstitution, substitution, isLastStatementInMmProof);
		this.stack.push(assertionStatementWithSubstitution);
	}
	//#endregion addSingleStepToMmpProof

	private addMmpStatementsFromMmStatementsInTheProof(provableStatement: ProvableStatement,
		mmProof: Statement[]) {
		this.addEHypMmpProofSteps(provableStatement);
		mmProof.forEach((statement: Statement, i: number) => {
			if (statement instanceof FHyp) {
				this.stack.push(statement.formula);
			} else if (statement instanceof EHyp) {
				//TODO1 20 MAY add eHyp MmpProofStep
				// this.addEHypMmpProofStep(statement);
				this.stack.push(statement.formula);
			} else if (statement instanceof ZIStatement) {
				this.stored.push(this.stack[this.stack.length - 1]);
			} else if (statement instanceof ZRStatement) {
				this.stack.push(this.stored[(<ZRStatement>statement).referencedZ]);
			} else if (statement instanceof AssertionStatement)
				this.addSingleStepToMmpProof(<AssertionStatement>statement,
					i == mmProof.length - 1);
		});
	}
	getMmStatementsFromCompressedProof(provableStatement: ProvableStatement): Statement[] {
		const proofCompressor: ProofCompressor = new ProofCompressor([]);
		const mmStatements: Statement[] = proofCompressor.DecompressProof(provableStatement,
			this.labelToStatementMap);
		return mmStatements;
	}
	private addMmpStatements(provableStatement: ProvableStatement) {
		//TODO this method works for normal proofs and compressed proofs, check if it works for packed proofs, too
		const mmStatements: Statement[] = provableStatement.hasCompressedProof
			? this.getMmStatementsFromCompressedProof(provableStatement)
			: Verifier.GetProofStatements(
				provableStatement.Proof,
				this.labelToStatementMap,
				provableStatement.ParentBlock ?? this.outermostBlock
			);
		this.addMmpStatementsFromMmStatementsInTheProof(provableStatement, mmStatements);
	}

	//#endregion addMmpStatements

	//#region addDisjStatements
	buildStatementTokens(var1: string, var2: string): MmToken[] {
		const statementTokens: MmToken[] = [
			new MmToken('$', 0, 0),
			new MmToken(var1, 0, 2),
			new MmToken(var2, 0, 4)
		];
		return statementTokens;
	}
	addDisjStatements(provableStatement: ProvableStatement) {
		const sortedDisjVarPairs: Array<[string, string]> = provableStatement.frame!.disjVars.sortedDisjVarPairs;
		for (const [var1, var2] of sortedDisjVarPairs) {
			const statement: MmToken[] = this.buildStatementTokens(var1, var2);
			this.mmpProof.addDisjointVarStatement(statement);
		}
	}
	//#endregion addDisjStatements

	buildProofForProvableStatement(provableStatement: ProvableStatement): MmpProof {
		this.addHeaderStatements(provableStatement);
		this.addMmpStatements(provableStatement);
		this.addDisjStatements(provableStatement);
		return this.mmpProof;
	}
	//#endregion buildProofForProvableStatement

	buildProof(): MmpProof | undefined {
		let mmpProof: MmpProof | undefined;
		const provableStatement: LabeledStatement | undefined =
			this.labelToStatementMap.get(this.theoremLabel);
		if (provableStatement instanceof ProvableStatement)
			mmpProof = this.buildProofForProvableStatement(provableStatement);
		return mmpProof;
	}
	//#endregion buildProof
}