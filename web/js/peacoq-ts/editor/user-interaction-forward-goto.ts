import * as CoqtopInput from "../coqtop-input";
import * as Global from "../global-variables";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

export function setupUserInteractionForwardGoto(
  forwardGoto$: Rx.Observable<AceAjax.Position>,
  editCreated$: Rx.Observable<IEdit<IEditStage>>,
  error$: Rx.Observable<IValueFail>
): Rx.Observable<{}> {

  return forwardGoto$.flatMap(dest => {
    return editCreated$
      // stop if the edit created ends after the destination position
      .takeWhile(e => isBefore(Strictly.Yes, e.stopPosition, dest))
      // stop if there's no text between the last edit and the destination
      .takeWhile(e => {
        const range = AceAjax.Range.fromPoints(e.stopPosition, dest);
        const text = Global.coqDocument.session.getDocument().getTextRange(range);
        return CoqStringUtils.coqTrimLeft(text) !== "";
      })
      // if an error occurs, abort
      .takeUntil(error$)
      // if another goto command occurs, abort and let the other one do the work
      .takeUntil(forwardGoto$)
      .map(_ => ({}))
      .startWith({})
  }).share();

}
