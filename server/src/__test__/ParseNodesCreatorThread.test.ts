import { GrammarManager, MmpRule } from '../grammar/GrammarManager';
import { InternalNode } from '../grammar/ParseNode';
import { LabeledStatement } from '../mm/LabeledStatement';
import { MmParser } from '../mm/MmParser';
import { GrammarManagerForThread, IMmpRuleForThread } from '../parseNodesCreatorThread/GrammarManagerForThread';
import { ParseNodeForThread } from '../parseNodesCreatorThread/ParseNodeForThread';

import {
	addParseNodes,
	createParseNodesInANewThread,
	createLabelToFormulaMap,
	createLabelToParseNodeForThreadMap,
	defaultProgressCallback,
	postMessage,
	createMessageLog
} from '../parseNodesCreatorThread/ParseNodesCreator';

import { eqeq1iMmParser } from './GlobalForTest.test';
import * as worker_threads from 'worker_threads';


function buildParseNodesSimulated(mmParser: MmParser) {
	const labelToFormulaMap: Map<string, string> = createLabelToFormulaMap(mmParser);
	const mmpRulesForThread: IMmpRuleForThread[] =
		GrammarManagerForThread.convertMmpRules(<MmpRule[]>mmParser.grammar.rules);
	const labelToParseNodeForThreadMap: Map<string, ParseNodeForThread> = createLabelToParseNodeForThreadMap(
		labelToFormulaMap,
		mmpRulesForThread,
	);

	addParseNodes(labelToParseNodeForThreadMap, mmParser.labelToStatementMap);
}

describe("ParseNodesCreator.ts", () => {

	beforeEach(() => {
		expect(worker_threads.parentPort).toBeNull();
	});

	afterEach(() => {
		(worker_threads.parentPort as unknown) = null;
	});

	test("Simulate working thread serialization, deserialization", () => {
		const postMessageMock = jest.fn();
		(worker_threads.parentPort as unknown) = {postMessage: postMessageMock};

		const mmParser: MmParser = eqeq1iMmParser;

		mmParser.createParseNodesForAssertionsSync();
		const dummyNode: InternalNode = new InternalNode('dummy', 'dummy', []);
		const labelToParseNode: Map<string, InternalNode> = new Map<string, InternalNode>();
		mmParser.labelToStatementMap.forEach((labeledStatement: LabeledStatement, label: string) => {
			if (MmParser.isParsable(labeledStatement)) {
				labelToParseNode.set(label, labeledStatement.parseNode!);
				labeledStatement.setParseNode(dummyNode);

			}
		});
		buildParseNodesSimulated(mmParser);
		const parseNode: InternalNode = labelToParseNode.get('axext3')!;
		const parseNodeSimulated: InternalNode = mmParser.labelToStatementMap.get('axext3')!.parseNode!;
		const areEqual: boolean = GrammarManager.areParseNodesEqual(parseNode, parseNodeSimulated);
		expect(areEqual).toBeTruthy();

		const messages = postMessageMock.mock.calls.map(call => call[0]);
		const logMessages = messages.filter(message => message.kind === 'log');
		const progressMessages = messages.filter(message => message.kind === 'progress');
		const doneMessages = messages.filter(message => message.kind === 'done');

		expect(logMessages).toEqual([
			{
				kind: 'log',
				text: 'labelToParseNodeForThreadMap.size = 391'
			},
			{
				kind: 'log',
				text: 'formulaToParseNodeForThreadCache.size = 181'
			}
		]);

		expect(progressMessages.length).toEqual(391);
		expect(doneMessages).toEqual([]);
	});

	describe("createParseNodesInANewThread", () => {
		const origWorker = worker_threads.Worker;

		afterEach(() => {
			(worker_threads.Worker as unknown) = origWorker;
		});

		it ("resolves when it recieves a MessageDone", async () => {
			let onMessage: any = undefined;

			(worker_threads.Worker as unknown) = jest.fn().mockImplementation(() => {
				return {
					on: (eventName: string, fn: unknown) => {
						if (eventName === 'message') {
							onMessage = fn;
						}
					}
				};
			});

			const promise = createParseNodesInANewThread(eqeq1iMmParser, defaultProgressCallback);
			const labelToParseNodeForThreadMap = new Map<string, ParseNodeForThread>();
			onMessage({kind: 'done', labelToParseNodeForThreadMap});
			await expect(promise).resolves.toBeUndefined();
		});
	});


	describe("postMessage", () => {

		it("posts a log message", () => {
			const postMessageMock = jest.fn();
			(worker_threads.parentPort as unknown) = {postMessage: postMessageMock};
			postMessage(createMessageLog('a log message'));
			expect(postMessageMock).toHaveBeenCalledWith({kind: 'log', text: 'a log message'});
		});

		it(`doesn't fail if there is no parentPort`, () => {
			expect(worker_threads.parentPort).toBeNull();
			postMessage(createMessageLog('a log message'));
		});


	});	
});
