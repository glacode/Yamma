import { Grammar } from 'nearley';
import { isMainThread, parentPort, Worker, workerData } from 'worker_threads';
import { MmpRule } from '../grammar/GrammarManager';
import { MmLexer } from '../grammar/MmLexer';
import { InternalNode, ParseNode } from '../grammar/ParseNode';
import { LabeledStatement, ParseResult } from '../mm/LabeledStatement';
import { MmParser } from '../mm/MmParser';
import { concatWithSpaces, notifyProgress } from '../mm/Utils';
import { WorkingVars } from '../mmp/WorkingVars';
import { GrammarManagerForThread, IMmpRuleForThread } from './GrammarManagerForThread';
import { ParseNodeForThread, ParseNodeForThreadConverter } from './ParseNodeForThread';

type MessageProgress = {
	kind: 'progress',
	index: number,
	count: number,
}

type MessageLog = {
	kind: 'log',
	text: string,
}

type MessageDone = {
	kind: 'done',
	labelToParseNodeForThreadMap: Map<string, ParseNodeForThread>,
}

type Message = MessageDone | MessageProgress | MessageLog;

export type ProgressCallback = (message: MessageProgress | MessageLog) => void;

export const createMessageProgress = (index: number, count: number): MessageProgress => {
	return {kind: 'progress', index, count};
};

export const createMessageLog = (text: string): MessageLog => {
	return {kind: 'log', text};
};

export const createMessageDone = (labelToParseNodeForThreadMap: Map<string, ParseNodeForThread>): MessageDone => {
	return {kind: 'done', labelToParseNodeForThreadMap};
};

export const postMessage = (message: Message) => {
	parentPort?.postMessage(message);
};

export const defaultProgressCallback: ProgressCallback = (message) => {
	switch(message.kind) {
		case 'progress':
			notifyProgress(message.index, message.count);
			break;
		case 'log':
			console.log(message.text);
			break;
	}
};

//#region CHILD THREAD
if (!isMainThread) {
	const { labelToFormulaMap, mmpRulesForThread }: { labelToFormulaMap: Map<string, string>, mmpRulesForThread: IMmpRuleForThread[] } = workerData;

	postMessage(createMessageLog('I am the worker thread!!!!!!!!!'));
	postMessage(createMessageLog('Worker thread!!!!: labelToFormulaMap.size = ' + labelToFormulaMap.size));
	const labelToParseNodeForThreadMap: Map<string, ParseNodeForThread> =
		createLabelToParseNodeForThreadMap(labelToFormulaMap, mmpRulesForThread);
	postMessage(createMessageDone(labelToParseNodeForThreadMap));
}

//#region createLabelToParseNodeForThreadMap

function createGrammar(mmpRulesForThread: IMmpRuleForThread[], workingVars: WorkingVars): Grammar {
	const mmpRules: MmpRule[] = GrammarManagerForThread.convertMmpRulesForThread(mmpRulesForThread);
	const grammar: Grammar = new Grammar(mmpRules);
	grammar.lexer = new MmLexer(workingVars);
	return grammar;
}

// export for testing, only
export function createParseNodeForThread(formula: string, grammar:
	Grammar, workingVars: WorkingVars): ParseNodeForThread | undefined {
	let parseNodeForThread: ParseNodeForThread | undefined;
	const parseResult: ParseResult = LabeledStatement.parseString(formula, grammar, workingVars);
	if (parseResult.parseNode != undefined)
		parseNodeForThread = ParseNodeForThreadConverter.convertParseNode(parseResult.parseNode);
	return parseNodeForThread;
}

function getParseNodeForThread(formula: string, grammar: Grammar, workingVars: WorkingVars,
	formulaToParseNodeForThreadCache: Map<string, ParseNodeForThread>): ParseNodeForThread | undefined {
	let parseNodeForThread: ParseNodeForThread | undefined = formulaToParseNodeForThreadCache.get(formula);
	if (parseNodeForThread == undefined) {
		const parseResult: ParseResult = LabeledStatement.parseString(formula, grammar, workingVars);
		parseNodeForThread = parseResult.parseNode;
		if (parseNodeForThread != undefined)
			formulaToParseNodeForThreadCache.set(formula, parseNodeForThread);
	}
	return parseNodeForThread;
}

// export for testing, only
export function createLabelToParseNodeForThreadMap(
	labelToFormulaMap: Map<string, string>,
	mmpRulesForThread: IMmpRuleForThread[],
	progressCallback: ProgressCallback = postMessage
): Map<string, ParseNodeForThread> {
	const labelToParseNodeForThreadMap: Map<string, ParseNodeForThread> = new Map<string, ParseNodeForThread>();
	const workingVars: WorkingVars = new WorkingVars(new Map<string, string>());
	const grammar: Grammar = createGrammar(mmpRulesForThread, workingVars);
	const formulaToParseNodeForThreadCache: Map<string, ParseNodeForThread> = new Map<string, ParseNodeForThread>();
	let i = 0;
	labelToFormulaMap.forEach((formula: string, label: string) => {
		progressCallback(createMessageProgress(i++, labelToFormulaMap.size));
		// comment out the following line to avoid caching
		const parseNodeForThread: ParseNodeForThread | undefined = getParseNodeForThread(
			formula, grammar, workingVars, formulaToParseNodeForThreadCache);
		// uncomment the following line to avoid caching
		// let parseNodeForThread: ParseNodeForThread | undefined = LabeledStatement.parseString(formula, grammar, workingVars);

		if (parseNodeForThread != undefined)
			labelToParseNodeForThreadMap.set(label, parseNodeForThread);
	});

	progressCallback(createMessageLog('labelToParseNodeForThreadMap.size = ' + labelToParseNodeForThreadMap.size));
	progressCallback(createMessageLog('formulaToParseNodeForThreadCache.size = ' + formulaToParseNodeForThreadCache.size));

	return labelToParseNodeForThreadMap;
}
//#endregion createLabelToParseNodeForThreadMap

//#endregion CHILD THREAD

//#region createParseNodesInANewThread
// export for testing, only
export function createLabelToFormulaMap(mmParser: MmParser): Map<string, string> {
	const labelToStatementMap: Map<string, LabeledStatement> = mmParser.labelToStatementMap;
	const labelToFormulaMap: Map<string, string> = new Map<string, string>();
	labelToStatementMap.forEach((labeledStatement: LabeledStatement) => {
		if (MmParser.isParsable(labeledStatement)) {
			const formula: string = concatWithSpaces(labeledStatement.formula);
			labelToFormulaMap.set(labeledStatement.Label, formula);
		}
	});
	return labelToFormulaMap;
}

// export for testing, only
export function addParseNodes(labelToParseNodeForThreadMap: Map<string, ParseNodeForThread>,
	labelToStatementMap: Map<string, LabeledStatement>) {
	// let i = 0;
	labelToParseNodeForThreadMap.forEach((parseNodeForThread: ParseNodeForThread, label: string) => {
		// notifyProgress(i++, labelToParseNodeForThreadMap.size);
		const parseNode: ParseNode = ParseNodeForThreadConverter.convertParseNodeForThread(parseNodeForThread);
		const labeledStatement: LabeledStatement | undefined = labelToStatementMap.get(label);
		if (labeledStatement != undefined)
			labeledStatement.setParseNode(<InternalNode>parseNode);
	});
}

export function createParseNodesInANewThread(mmParser: MmParser, progressCallback: ProgressCallback ): Promise<void> {
	// This code is executed in the main thread and not in the worker.
	const labelToFormulaMap: Map<string, string> = createLabelToFormulaMap(mmParser);
	const mmpRulesForThread: IMmpRuleForThread[] =
		GrammarManagerForThread.convertMmpRules(<MmpRule[]>mmParser.grammar.rules);

	progressCallback(createMessageLog('I am the Main thread!!!!!!!: labelToFormulaMap.size = ' + labelToFormulaMap.size));

	// Create the worker.
	const workerFileName: string = __filename.replace('src', 'out').replace('.ts', '.js');
	// const worker = new Worker(__filename);
	// let workerData: any = { parseNode: labelToStatementMap };
	const workerData = { labelToFormulaMap: labelToFormulaMap, mmpRulesForThread: mmpRulesForThread };
	const worker = new Worker(workerFileName, { workerData: workerData });

	return new Promise<void>(resolve => {
		// Listen for messages from the worker and print them.
		worker.on('message', (message: Message) => {
			if (message.kind === 'done') {
				progressCallback(createMessageLog('I am back to the Main thread!!!!!!!'));
				addParseNodes(message.labelToParseNodeForThreadMap, mmParser.labelToStatementMap);
				resolve();
				mmParser.areAllParseNodesComplete = true;
			} else {
				progressCallback(message);
			}
		});
	});
}
//#endregion createParseNodesInANewThread

export function createParseNodesInCurrentThread(mmParser: MmParser, progressCallback: ProgressCallback ): void {
	const labelToFormulaMap: Map<string, string> = createLabelToFormulaMap(mmParser);
	const mmpRulesForThread: IMmpRuleForThread[] =
		GrammarManagerForThread.convertMmpRules(<MmpRule[]>mmParser.grammar.rules);

	createLabelToParseNodeForThreadMap(labelToFormulaMap, mmpRulesForThread, progressCallback);
	mmParser.areAllParseNodesComplete = true;
}

// function createParseNodes(): any {
// 	GlobalState.lastMmpParser!.labelToStatementMap.forEach((labeledStatement: LabeledStatement) => {
// 		if (labeledStatement instanceof EHyp ||
// 			labeledStatement instanceof AssertionStatement && !GrammarManager.isSyntaxAxiom2(labeledStatement)) {
// 			// if the parseNode is undefined, it will create it
// 			labeledStatement.parseNode;
// 		}
// 	});
// }
