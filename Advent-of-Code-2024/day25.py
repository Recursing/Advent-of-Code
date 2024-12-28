from typing import Literal


text = open(__file__.replace(".py", ".txt")).read()

widgets = [widget.split("\n") for widget in text.split("\n\n")]


def parse(widget: list[str]) -> tuple[Literal["key", "lock"], list[int]]:
    widget_type: Literal["key", "lock"] = "lock" if widget[0] == "#####" else "key"
    if widget_type == "key":
        assert widget[-1] == "#####"
    return (widget_type, [col.count("#") - 1 for col in zip(*widget)])


parsed_widgets = [parse(widget) for widget in widgets]
keys = [w for t, w in parsed_widgets if t == "key"]
locks = [w for t, w in parsed_widgets if t == "lock"]
fits = 0
for key in keys:
    for lock in locks:
        if all(a + b <= 5 for a, b in zip(key, lock)):
            fits += 1

print(fits)
