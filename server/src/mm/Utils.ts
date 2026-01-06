import { Connection, Diagnostic, MessageActionItem, Position, Range, TextEdit, TextEditChange, WorkspaceChange } from 'vscode-languageserver';
import { MmToken } from '../grammar/MmLexer';
import { MmpParserErrorCode, MmpParserWarningCode } from '../mmp/MmpParser';
import { MmParserErrorCode } from './MmParser';





export function AreArrayTheSame(array1: any[], array2: any[]) {
    return (array1.length == array2.length) && array1.every(function (element, index) {
        return element === array2[index];
    });
}

/**
 * Splits a string and also returns the position of each substring
 * @param str string to be split
 * @param regex regular expression to match (the negation of the separator)
 * @returns two arrays: the substrings and their position in the original string
 */
export function splitWithPosition(str: string, regex: RegExp): { subStrings: string[], positions: number[] } {
    const subStrings: string[] = [];
    const positions: number[] = [];
    let nextMatch: RegExpExecArray | null;
    nextMatch = regex.exec(str);
    while (nextMatch != null) {
        subStrings.push(nextMatch[0]);
        positions.push(nextMatch.index);
        nextMatch = regex.exec(str);
    }
    return { subStrings: subStrings, positions: positions };
}

/**
 * Splits a string and also returns the position of each substring
 * @param str string to be split
 * @param regex regular expression to match (the negation of the separator)
 * @returns an array of tokens (string and starting position)
 */
export function splitToTokens(str: string, regex: RegExp,
    currentLine: number, fistCharColumn: number): MmToken[] {
    const result: MmToken[] = [];
    let nextMatch: RegExpExecArray | null;

    nextMatch = regex.exec(str);
    while (nextMatch != null) {
        // subStrings.push(nextMatch[0])
        // positions.push(nextMatch.index)
        const tokenColumn = nextMatch.index + fistCharColumn;
        const token: MmToken = new MmToken(nextMatch[0], currentLine, tokenColumn);
        result.push(token);
        nextMatch = regex.exec(str);
    }
    return result;
}

export function splitToTokensDefaultInLine(str: string, line: number): MmToken[] {
    const result = splitToTokens(str, /[^\s]+/g, line, 0);
    return result;
}

export function splitToTokensDefaultInLineColumn(str: string, line: number, fistCharColumn: number): MmToken[] {
    const result = splitToTokens(str, /[^\s]+/g, line, fistCharColumn);
    return result;
}

export function splitToTokensAllowingForEmptyValues(str: string, separator: string, line: number, fistCharColumn: number): MmToken[] {
    const result: MmToken[] = [];
    let i = 0;
    let j = 0;
    while (j < str.length) {
        j = str.indexOf(separator, i);
        if (j === -1)
            // the end of str has been reached
            j = str.length;
        const newToken = new MmToken(str.substring(i, j), line, fistCharColumn + i);
        result.push(newToken);
        i = j + 1;
    }
    return result;
}

/**
 * Splits a string with respect to blank separators and also returns the position of each substring
 * @param str string to be split
 * @returns 
 */
export function splitToTokensDefault(str: string): MmToken[] {
    const result: MmToken[] = [];
    let nextMatch: RegExpExecArray | null;
    const regExp = /[^\s]+/g;

    nextMatch = regExp.exec(str);
    while (nextMatch != null) {
        // subStrings.push(nextMatch[0])
        // positions.push(nextMatch.index)
        const tokenColumn = nextMatch.index;
        const token: MmToken = new MmToken(nextMatch[0], 0, tokenColumn);
        result.push(token);
        nextMatch = regExp.exec(str);
    }
    return result;
}

/**
 * Retuns the range of a string
 * @param token string for wich the range has to be computed
 * @param line the string is assumed to be on a single line
 * @param startCharacter the column where the string begins
 */
export function range(token: string, line: number, startCharacter: number): Range {
    const startPosition: Position = { line: line, character: startCharacter };
    const endPosition: Position = { line: line, character: startCharacter + token.length };
    const result: Range = { start: startPosition, end: endPosition };
    return result;
}

export function currentDateTimeWithMilliseconds() {
    const now = new Date();
    const year = now.getFullYear();
    const month = String(now.getMonth() + 1).padStart(2, '0');
    const day = String(now.getDate()).padStart(2, '0');
    const hours = String(now.getHours()).padStart(2, '0');
    const minutes = String(now.getMinutes()).padStart(2, '0');
    const seconds = String(now.getSeconds()).padStart(2, '0');
    const milliseconds = String(now.getMilliseconds()).padStart(3, '0');

    const dateTimeWithMilliseconds = `${year}-${month}-${day} ${hours}:${minutes}:${seconds}.${milliseconds}`;

    return dateTimeWithMilliseconds;
}

export function consoleLogWithTimestamp(message: string) {
    const dateTimeWithMilliseconds = currentDateTimeWithMilliseconds();
    // const timeStamp = "[" + new Date().toTimeString() + "]";
    const timeStamp = "[ " + dateTimeWithMilliseconds + " ]";
    const messageWithTimeStamp: string = timeStamp + " " + message;
    console.log(messageWithTimeStamp);
}

export function notifyProgressWithTimestampAndMemory(message: string, current: number, total: number) {
    const previousPercentageOfWorkDone: number = Math.trunc(((current - 1) * 100) / total);
    const percentageOfWorkDone: number = Math.trunc((current * 100) / total);
    if (previousPercentageOfWorkDone < percentageOfWorkDone) {
        const used: number = process.memoryUsage().heapUsed / 1024 / 1024;
        const total: number = process.memoryUsage().heapTotal / 1024 / 1024;
        const memory = `Memory heap used/total ${Math.round(used * 100) / 100} MB / ${Math.round(total * 100) / 100}`;
        console.log(`The script uses approximately ${Math.round(used * 100) / 100} MB`);
        console.log(message + '-' + percentageOfWorkDone + '% - ' + memory + '-' + new Date());
    }
}

/**
 * Concats strings adding a space between each of them
 * @param stringArray array of strings to concat
 */
export function concatWithSpaces(stringArray: string[]): string {
    let result = "";
    // stringArray.forEach(str => { result = result.concat(...[' ', str]); });
    result = stringArray.join(" ");
    return result;
}

/** builds a formula where each symbol is surrounded exactly by one space,
 * on both side
 */
export function normalizedFormula(stringArray: string[]): string {
    const result: string = " " + concatWithSpaces(stringArray) + " ";
    return result;
}

/**
 * Concats strings adding a space between each of them, but skips the first skip items
 * @param skip numbero of elements to skip
 * @param stringArray 
 * @returns 
 */
export function concatWithSpacesSkippingStart(skip: number, stringArray: string[]): string {
    let result = "";
    if (stringArray.length > skip)
        result = stringArray[skip];
    for (let i = skip + 1; i < stringArray.length; i++)
        result = result + " " + stringArray[i];
    // tokens.forEach(token => { result = result.concat(...[' ', token.value]); });
    return result;
}

/**
 * Concats strings adding a comma between each of them
 * @param stringArray 
 * @returns 
 */
export function concatWithCommas(stringArray: string[]): string {
    let result = "";
    stringArray.forEach(str => { result = result.concat(...[',', str]); });
    return result;
}


/**
 * Concats token values adding the given separatore between each of them
 * @param tokens array of tokens to concat
 * @param separator separator to be added between tokens
 * @returns a string where token values are concatenated, separated by the separator
 */
export function concatTokenValuesWithSeparator(tokens: MmToken[], separator: string): string {
    let result = "";
    if (tokens.length > 0)
        result = tokens[0].value;
    for (let i = 1; i < tokens.length; i++) {
        // const element = tokens[i];
        result = result + separator + tokens[i].value;
    }
    // tokens.forEach(token => { result = result.concat(...[' ', token.value]); });
    return result;
}

export function concatTokenValuesOrUndefinedWithSeparator(tokens: (MmToken | undefined)[], separator: string): string {
    let result = "";
    if (tokens.length > 0) {
        result = (tokens[0] instanceof MmToken ? tokens[0].value : '');
    }
    for (let i = 1; i < tokens.length; i++) {
        const valueToConcat = (tokens[i] instanceof MmToken ? (<MmToken>tokens[i]).value : '');
        result = result + separator + valueToConcat;
    }
    // tokens.forEach(token => { result = result.concat(...[' ', token.value]); });
    return result;
}

//TODO use concatTokenValuesWithSeparator to implement this one, then rerun all tests
/**
 * Concats token values adding a space between each of them
 * @param tokens array of tokens to concat
 * @returns 
 */
export function concatTokenValuesWithSpaces(tokens: MmToken[]): string {
    let result = "";
    if (tokens.length > 0)
        result = tokens[0].value;
    for (let i = 1; i < tokens.length; i++) {
        // const element = tokens[i];
        result = result + " " + tokens[i].value;
    }
    // tokens.forEach(token => { result = result.concat(...[' ', token.value]); });
    return result;
}

/**
 * returns a one character range, starting at position
 * @param position the starting position for the one character range
 * @returns 
 */
export function oneCharacterRange(position: Position): Range {
    const start: Position = position;
    const end: Position = { line: position.line, character: position.character + 1 };
    const range: Range = { start: start, end: end };
    return range;
}

export const dummyRange: Range = oneCharacterRange({ line: 0, character: 0 });

export function dummyToken(value: string): MmToken {
    return new MmToken(value, 0, 0);
}


export function removeItemsFromEndOfArray(array: any[], numberOfElementsToBeRemoved: number) {
    const startIndexFroSplice: number = array.length - numberOfElementsToBeRemoved;
    array.splice(startIndexFroSplice, numberOfElementsToBeRemoved);
}


/** rebuilds the original string, inserting the right number of spaces and of endOfLine characters */
export function rebuildOriginalStringFromTokens(tokens: MmToken[]): string {
    let result = '';
    if (tokens.length > 0)
        result = ' '.repeat(tokens[0].range.start.character) + tokens[0].value;
    for (let i = 0; i < tokens.length - 1; i++) {
        const currentToken = tokens[i + 1];
        const previousToken = tokens[i];
        let spaces: string;
        if (previousToken.range.end.line < currentToken.range.start.line) {
            // the current token is on a new line
            result += '\n'; // we are assuming there are no empty lines
            spaces = ' '.repeat(currentToken.range.start.character);
        } else
            // the current token is on the same line as the previous one
            spaces = ' '.repeat(currentToken.range.start.character - previousToken.range.end.character);
        result += spaces + currentToken.value;
    }
    return result;
}

export function doesDiagnosticsContain(diagnostics: Diagnostic[],
    errorCode: MmpParserErrorCode | MmpParserWarningCode | MmParserErrorCode): boolean {
    let containsErrorCode = false;
    let i = 0;
    while (!containsErrorCode && i < diagnostics.length) {
        containsErrorCode ||= diagnostics[i].code == errorCode;
        i++;
    }
    return containsErrorCode;
}

export function fromTokensToStrings(tokens: MmToken[]): string[] {
    return MmToken.fromTokensToStrings(tokens);
}

export function fromStringsToTokens(stringArray: string[]): MmToken[] {
    const str: string = concatWithSpaces(stringArray);
    const tokens: MmToken[] = splitToTokensDefault(str);
    return tokens;
}

/** returns the range of the whole array of tokens; it cannot be invoked with empty arrays */
export function arrayRange(tokens: MmToken[]): Range {
    if (tokens.length == 0)
        throw new Error("This function should be invoked only with non empty arrays");
    // let range: Range | undefined = defaultRange;
    // if (tokens.length > 0) {
    const start: Position = tokens[0].range.start;
    const end: Position = tokens[tokens.length - 1].range.end;
    const range = { start: start, end: end };
    // }
    return range;
}

export function notifyInformation(informationMessage: string, connection: Connection) {
    const messageActionItem: MessageActionItem = { title: "Ok" };
    const messageActionItems: MessageActionItem[] = [messageActionItem];
    connection.window.showInformationMessage(informationMessage, ...messageActionItems);
}

export function notifyShortInformation(informationMessage: string, connection: Connection) {
    connection.window.showInformationMessage(informationMessage);
}

export function notifyWarning(warningMessage: string, connection: Connection) {
    const messageActionItem: MessageActionItem = { title: "Ok" };
    const messageActionItems: MessageActionItem[] = [messageActionItem];
    connection.window.showWarningMessage(warningMessage, ...messageActionItems);
}

export function notifyError(errorMessage: string, connection: Connection) {
    const messageActionItem: MessageActionItem = { title: "Ok" };
    const messageActionItems: MessageActionItem[] = [messageActionItem];
    connection.window.showErrorMessage(errorMessage, ...messageActionItems);
}


//#region intersection

/** true if element is in all sets in set, without considering firstSet */
function isInIntersection<T>(element: T, set: Set<Set<T>>): boolean {
    let result = true;
    //TODO using arrays instead of sets and a while loop could be much more efficient
    set.forEach((intersectingSet: Set<T>) => {
        result &&= intersectingSet.has(element);
    });
    return result;

}
/** returns the intersection of a (finite) set ; if the set is empty,
 * we return undefined
*/
export function intersection<T>(set: Set<Set<T>>): Set<T> | undefined {
    let result: Set<T> | undefined;
    if (set.size > 0) {
        result = new Set<T>();
        const [firstSet] = set;
        firstSet.forEach((element: T) => {
            if (isInIntersection<T>(element, set))
                result?.add(element);
        });
    }
    return result;
}
//#endregion intersection

export function intersection2<T>(a: Set<T>, b: Set<T>): Set<T> {
    const set: Set<Set<T>> = new Set<Set<T>>().add(a).add(b);
    const result: Set<T> = intersection(set)!;
    return result;
}

export function subset<T>(a: Set<T>, b: Set<T>): boolean {
    const isSubset: boolean = Array.from(a).every(val => b.has(val));
    return isSubset;
}

export function union2<T>(a: Set<T>, b: Set<T>): Set<T> {
    const union = new Set([...a, ...b]);
    return union;
}

export function difference<T>(a: Set<T>, b: Set<T>): Set<T> {
    const difference = new Set(
        [...a].filter(x => !b.has(x)));
    return difference;
}

export function notifyProgress(current: number, total: number, message?: string) {
    const previousPercentageOfWorkDone: number = Math.trunc(((current - 1) * 100) / total);
    const percentageOfWorkDone: number = Math.trunc((current * 100) / total);
    const completeMessage: string | number =
        (message != undefined ? message + " - " + percentageOfWorkDone : percentageOfWorkDone);
    if (previousPercentageOfWorkDone < percentageOfWorkDone)
        // consoleLogWithTimestamp(percentageOfWorkDone + '%');
        consoleLogWithTimestamp(completeMessage + '%');
}

export async function applyTextEdits(textEdits: TextEdit[], textDocumentUri: string, connection: Connection) {
    const workspaceChange: WorkspaceChange = new WorkspaceChange();
    const textEditChange: TextEditChange = workspaceChange.getTextEditChange(
        // this.searchCommandParameter.uri);
        textDocumentUri);
    textEdits.forEach((textEdit: TextEdit) => {
        textEditChange.add(textEdit);
    });
    // textEditChange.insert(insertPosition, searchStatement);
    await connection.workspace.applyEdit(workspaceChange.edit);
}

export function updateOccurrences<T>(map: Map<T, number>, key: T): Map<T, number> {
    const currentValue: number = map.get(key) || 0;
    map.set(key, currentValue + 1);
    return map;
}
