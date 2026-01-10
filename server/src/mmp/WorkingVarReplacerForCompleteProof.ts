import { MmpProof } from './MmpProof';
import { IMmpStatement } from './MmpStatement';
import { MmpProofStep } from './MmpProofStep';
import { InternalNode, ParseNode } from '../grammar/ParseNode';
import { GrammarManager } from '../grammar/GrammarManager';
import { WorkingVarsUnifierApplier } from './WorkingVarsUUnifierApplier';
import { MmToken } from '../grammar/MmLexer';
import { FormulaToParseNodeCache } from './FormulaToParseNodeCache';
import { Diagnostic } from 'vscode-languageserver';
import { MmpParserWarningCode } from './MmpParser';
import { MmpValidator } from './MmpValidator';

/**
 * This class provides methods to replace all working variables in a proof
 * with unused variables of the same kind from the theory.
 * This is needed when the proof is complete, but still contains working variables.
 */
export class WorkingVarReplacerForCompleteProof {
	constructor(private uProof: MmpProof) {
	}

	/**
	 * Recursive method that traverses the parse node and adds any working var found to the set
	 * @param parseNode the parse node to traverse
	 * @param workingVars the set of working vars to update
	 */
	private gatherWorkingVars(parseNode: InternalNode, workingVars: Map<string, InternalNode[]>) {
		parseNode.parseNodes.forEach((child: ParseNode) => {
			if (GrammarManager.isInternalParseNodeForWorkingVar(child)) {
				const workingVar: string = GrammarManager.getTokenValueFromInternalNode(<InternalNode>child);
				let internalNodes: InternalNode[] | undefined = workingVars.get(workingVar);
				if (internalNodes == undefined) {
					internalNodes = [];
					workingVars.set(workingVar, internalNodes);
				}
				internalNodes.push(<InternalNode>child);
			} else if (child instanceof InternalNode)
				this.gatherWorkingVars(child, workingVars);
		});
	}

	/**
	 * Returns the set of working vars present in the proof
	 */
	private getWorkingVars(): Map<string, InternalNode[]> {
		const workingVars: Map<string, InternalNode[]> = new Map<string, InternalNode[]>();
		this.uProof.mmpStatements.forEach((mmpStatement: IMmpStatement) => {
			if (mmpStatement instanceof MmpProofStep && mmpStatement.parseNode != undefined)
				this.gatherWorkingVars(mmpStatement.parseNode, workingVars);
		});
		return workingVars;
	}

	/**
	 * Returns the set of variables present in the proof. This is used to avoid using a variable
	 * that is already present in the proof (even if it is not mandatory)
	 */
	private getVarsPresentInProof(): Set<string> {
		const usedVars: Set<string> = new Set<string>();
		this.uProof.mmpStatements.forEach((mmpStatement: IMmpStatement) => {
			if (mmpStatement instanceof MmpProofStep && mmpStatement.parseNode != undefined) {
				const varsInStep = mmpStatement.parseNode.symbolsSubsetOf(this.uProof.outermostBlock.v);
				varsInStep.forEach(v => usedVars.add(v));
			}
		});
		return usedVars;
	}

	/**
	 * Returns a variable of the given kind that is not in the set of used variables
	 * @param kind the kind of the variable to find
	 * @param usedVars the set of used variables
	 */
	private findUnusedVar(kind: string, usedVars: Set<string>): string | undefined {
		const variables: Set<string> = this.uProof.outermostBlock.v;
		let unusedVar: string | undefined;
		// We iterate over all variables in the theory
		for (const variable of variables) {
			if (this.uProof.outermostBlock.kindOf(variable) == kind && !usedVars.has(variable)) {
				unusedVar = variable;
				break;
			}
		}
		return unusedVar;
	}

	/**
	 * Creates a parse node for the given variable, to be used as a replacement
	 * @param unusedVar the variable to create the node for
	 * @param kind the kind of the variable
	 * @returns the created InternalNode, or undefined if the variable definition cannot be found
	 */
	private createReplacementNode(unusedVar: string, kind: string): InternalNode | undefined {
		const fHyp = this.uProof.outermostBlock.varToFHypMap.get(unusedVar);
		if (fHyp) {
			const mmToken = new MmToken(unusedVar, 0, 0, kind);
			const replacementNode = new InternalNode(fHyp.Label, fHyp.Kind, [mmToken]);
			return replacementNode;
		}
		return undefined;
	}

	/**
	 * Builds the map of substitutions from working vars to theory vars
	 * @param workingVars the working variables to replace
	 * @param usedVars the variables currently used in the proof (updated in place)
	 * @returns a map where keys are working vars and values are their replacement nodes
	 */
	private buildUnifier(workingVars: Map<string, InternalNode[]>, usedVars: Set<string>,
		diagnostics?: Diagnostic[]): Map<string, InternalNode> {
		const unifier: Map<string, InternalNode> = new Map<string, InternalNode>();
		workingVars.forEach((internalNodes: InternalNode[], workingVar: string) => {
			const kind: string = <string>this.uProof.workingVars.kindOf(workingVar);
			const unusedVar: string | undefined = this.findUnusedVar(kind, usedVars);
			if (unusedVar == undefined) {
				if (diagnostics != undefined) {
					internalNodes.forEach((internalNode: InternalNode) => {
						const mmToken: MmToken = GrammarManager.getTokenFromInternalNode(internalNode);
						const message = `No unused variable of kind ${kind} found in the theory`;
						MmpValidator.addDiagnosticWarning(
							message,
							mmToken.range,
							MmpParserWarningCode.proofCompleteButWorkingVarsRemainAndNoUnusedTheoryVars,
							diagnostics );
					});
				}
			} else {
				const replacementNode = this.createReplacementNode(unusedVar, kind);
				if (replacementNode) {
					unifier.set(workingVar, replacementNode);
					usedVars.add(unusedVar);
				}
			}
		});
		return unifier;
	}

	/**
	 * Applies the unification substitution to the proof
	 * @param unifier the substitution map
	 * @param formulaToParseNodeCache optional cache to update
	 */
	private applyUnifier(unifier: Map<string, InternalNode>, formulaToParseNodeCache?: FormulaToParseNodeCache) {
		if (unifier.size > 0) {
			const unifierApplier: WorkingVarsUnifierApplier = new WorkingVarsUnifierApplier(
				unifier, this.uProof, formulaToParseNodeCache);
			unifierApplier.applyUnifier();
		}
	}

	/**
	 * Replaces all working vars in the proof with unused variables (in the theory) of the same kind.
	 * This is needed when the proof is complete, but still contains working variables.
	 * @param formulaToParseNodeCache if provided, the cache will be updated with the new formulas
	 */
	replaceWorkingVarsWithTheoryVars(formulaToParseNodeCache?: FormulaToParseNodeCache, diagnostics?: Diagnostic[]) {
		const workingVars: Map<string, InternalNode[]> = this.getWorkingVars();
		if (workingVars.size > 0) {
			const usedVars: Set<string> = this.getVarsPresentInProof();
			const unifier = this.buildUnifier(workingVars, usedVars, diagnostics);
			this.applyUnifier(unifier, formulaToParseNodeCache);
		}
	}

	/** adds diagnostics for working vars that cannot be replaced by an unused theory variable.
	 * This method is used when the prof is complete, but still contains working variables and
	 * there are no unused theory variables to replace them with.
	 * This method is called both from the MmpUnifier (to check if the proof can be generated) and
	 * from the MmpValidator (to add diagnostics after unification). When called from the MmpUnifier,
	 * the diagnostics are not sent to the editor, but only used to decide if the proof can be generated.
	 * Only when called from the MmpValidator, the diagnostics are actually sent to the editor.
	 */
	addDiagnosticsForMissingUnusedVars(diagnostics: Diagnostic[]) {
		const workingVars: Map<string, InternalNode[]> = this.getWorkingVars();
		if (workingVars.size > 0) {
			const usedVars: Set<string> = this.getVarsPresentInProof();
			this.buildUnifier(workingVars, usedVars, diagnostics);
		}
	}
}
