/** objects available in all modules, to avoid having frequently used parameters
 * to be passed to many classes / methods
 */

import { Connection, Range } from 'vscode-languageserver';
import { ConfigurationManager, IExtensionSettings } from '../mm/ConfigurationManager';
import { MmParser } from '../mm/MmParser';
import { MmStatistics } from '../mm/MmStatistics';
import { FormulaToParseNodeCache } from '../mmp/FormulaToParseNodeCache';
import { MmpParser } from '../mmp/MmpParser';
import { MmpStatistics } from '../mmp/MmpStatistics';
import { StepSuggestionMap } from '../stepSuggestion/StepSuggestionMap';

export class GlobalState {

	/** the path of the .mm file containing the current theory */
	mmFilePath?: string;

	/** the mmParser containing the current theory */
	mmParser?: MmParser;

	/** the statistics for the current theory */
	mmStatistics?: MmStatistics;

	/** the last MmpParser used for a validation of the current .mmp file */
	lastMmpParser?: MmpParser;

	/** the statistics for the mmp file */
	mmpStatistics?: MmpStatistics;

	/** maps every rpnSyntaxTree to a list of suggestion */
	stepSuggestionMap?: StepSuggestionMap;
	// static stepSuggestionMap: Map<string, IStepSuggestion[]>;

	/** the ConfigurationManager created in server.ts */
	configurationManager?: ConfigurationManager;

	/** last settings fetched by the configuration manager from the workspace configuration */
	lastFetchedSettings: IExtensionSettings | undefined;

	connection?: Connection;
	
	/** true iff the extension is loading a theory; used to avoid multiple loading
	 * triggered by different events
	 */
	loadingATheory = false;

	/** true iff a unify() has been performed, but the cursor has not been updated yet*/
	private _isCursorPositionUpdateRequired = false;


	public get isCursorPositionUpdateRequired() {
		const result: boolean = this._isCursorPositionUpdateRequired;
		this._isCursorPositionUpdateRequired = false;
		return result;
	}
	
	public requireCursorPositionUpdate() {
		this._isCursorPositionUpdateRequired = true;
	}

	/** true iff the last unification determined that the proof is complete,
	 * but it contains working variables, and there are no unused theory variables
	 * to replace them with. In this case, the user should be informed that he/she
	 * should manually replace the working variables in order to complete the proof.
	 * In most theories, this should never happen, in practice.
	 */
	public isProofCompleteAndItContainsWorkingVarsAndThereAreNoUnusedTheoryVars = false;


	suggestedRangeForCursorPosition?: Range;

	setSuggestedRangeForCursorPosition(range: Range | undefined) {
		this.suggestedRangeForCursorPosition = range;
	}

	isTriggerSuggestRequired = false;

	requireTriggerSuggest() {
		this.isTriggerSuggestRequired = true;
	}

	resetTriggerSuggest() {
		this.isTriggerSuggestRequired = false;
	}

	private _formulaToParseNodeCache?: FormulaToParseNodeCache;

	/** cache for formula recently parsed. It really speeds up the MmpParser, because
	 * it allows avoiding most of the parsing time (an .mmp file, often doesn't
	 * change much from an edit to the other)
	 */
	public get formulaToParseNodeCache(): FormulaToParseNodeCache {
		if (this._formulaToParseNodeCache == undefined)
			this._formulaToParseNodeCache = new FormulaToParseNodeCache();
		return this._formulaToParseNodeCache;
	}
}