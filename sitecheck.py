#!/usr/bin/env python3
"""公開前の Markdown と公開後の内部リンクを検査する。

SPDX-License-Identifier: MIT
"""

import argparse
import csv
import html
import os
import re
import signal
import sys
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from functools import cache
from html.parser import HTMLParser
from http.client import HTTPException
from pathlib import Path
from threading import current_thread, main_thread
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, urlsplit
from urllib.request import HTTPRedirectHandler, build_opener
from xml.etree import ElementTree


COMMAND_NAME = Path(__file__).stem
PRE_USAGE = f"使い方: {COMMAND_NAME} pre <下書き.md>"
POST_USAGE = (
    f"使い方: {COMMAND_NAME} post (--sitemap URL | --feed URL) "
    "[--format {markdown,csv}]"
)
ATX_HEADING = re.compile(r"^ {0,3}(#{1,6})(?:[ \t]|$)")
SETEXT_UNDERLINE = re.compile(r"^ {0,3}(=+|-+)[ \t]*$")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
PARAGRAPH_INTERRUPT = re.compile(
    r"^ {0,3}(?:>|<|(?:[-+*]|\d+[.)])(?:[ \t]|$)|(?:\*[ \t]*){3,}$|"
    r"(?:-[ \t]*){3,}$|(?:_[ \t]*){3,}$)"
)
ESCAPE = r"\\[!-`{-~]"
LABEL_TEXT = rf"(?:{ESCAPE}|[^\[\]\\]|\\)"
INLINE_MARK = re.compile(
    rf"{ESCAPE}|(?P<ticks>`+)|(?P<image>!)?\[(?P<label>(?:"
    rf"{LABEL_TEXT}|\[{LABEL_TEXT}*\])*)\]\("
)
TITLE = r"""(?:"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|\((?:\\.|[^()\\])*\))"""
HTTP_SCHEME = re.compile(r"^https?:", re.IGNORECASE)
COMPLETE_HTTP_SCHEME = re.compile(r"^https?://", re.IGNORECASE)
INCOMPLETE_SCHEME = re.compile(r"^(?:://|https?//)", re.IGNORECASE)
ESCAPED_PUNCTUATION = re.compile(ESCAPE)


@dataclass(frozen=True)
class Finding:
    line: int
    check: str
    detail: str
    # 警告はレポートに表示するが、終了コード 1 の判定には含めない。
    warning: bool = False


def content_lines(source: str) -> Iterator[str]:
    """コードブロックを空行に置き換え、元の行番号を保持する。"""
    fence = None
    for line in source.split("\n"):
        marker = FENCE.match(line)
        if fence:
            if (
                marker
                and marker[1][0] == fence[0]
                and len(marker[1]) >= len(fence)
                and not marker[2].strip()
            ):
                fence = None
            yield ""
        elif marker and (marker[1][0] == "~" or "`" not in marker[2]):
            fence = marker[1]
            yield ""
        elif re.match(r"^(?: {4}| {0,3}\t)", line):
            yield ""
        else:
            yield line


def is_empty_alt(label: str) -> bool:
    """装飾用途も含め、代替テキストが空の画像を指摘する。"""
    return not label.strip()


def url_problem(destination: str) -> str | None:
    """明示的な HTTP(S) 表記を検査し、スキーム相対 URL は許容する。"""
    if COMPLETE_HTTP_SCHEME.match(destination):
        if any(character.isspace() for character in destination):
            return "URL に空白が含まれています"
        # urlsplit は括弧の不整合など、対象外の体裁でも例外を出す。
        authority = re.split(r"[/#?]", destination.split("://", 1)[1], maxsplit=1)[0]
        try:
            host = urlsplit(destination).hostname
        except ValueError:
            host = authority.rsplit("@", 1)[-1]
        if not host:
            return "HTTP(S) URL のホストを入力してください"
    elif HTTP_SCHEME.match(destination) or INCOMPLETE_SCHEME.match(destination):
        return "HTTP(S) URL のスキームを http:// または https:// と表記してください"
    return None


def read_destination(line: str, start: int) -> tuple[str, int] | None:
    """括弧を対応させ、任意のタイトルをリンク先から取り除く。"""
    depth = 0
    index = start
    angle_end = None
    angle_start = start + len(line[start:]) - len(line[start:].lstrip(" \t"))
    if line[angle_start:angle_start + 1] == "<":
        angle = re.match(r"<(?:\\.|[^<>\\])*>", line[angle_start:])
        if angle is None:
            return None
        angle_end = angle_start + angle.end()
        index = angle_end

    while index < len(line):
        character = line[index]
        if character == "\\" and index + 1 < len(line):
            index += 2
            continue
        if depth == 0 and character in "\"'(" and index > angle_start and line[index - 1] in " \t":
            title = re.match(TITLE + r"[ \t]*\)", line[index:])
            if title and (angle_end is None or not line[angle_end:index].strip(" \t")):
                destination = line[start:index].strip(" \t")
                return normalize_destination(destination), index + title.end()
        if character == "(":
            depth += 1
        elif character == ")":
            if depth == 0:
                if angle_end is not None and line[angle_end:index].strip(" \t"):
                    return None
                destination = line[start:index].strip(" \t")
                return normalize_destination(destination), index + 1
            depth -= 1
        index += 1
    return None


def normalize_destination(destination: str) -> str:
    if destination.startswith("<") and destination.endswith(">"):
        destination = destination[1:-1]
    return html.unescape(ESCAPED_PUNCTUATION.sub(lambda match: match[0][1:], destination))


def inline_findings(line: str, number: int) -> Iterator[Finding]:
    cursor = 0
    while match := INLINE_MARK.search(line, cursor):
        cursor = match.end()
        if ticks := match["ticks"]:
            closing = re.search(rf"(?<!`){ticks}(?!`)", line[cursor:])
            if closing:
                cursor += closing.end()
            continue
        if match["label"] is None:
            continue
        result = read_destination(line, cursor)
        if result is None:
            continue
        destination, cursor = result
        label = match["label"]
        if match["image"]:
            if is_empty_alt(label):
                yield Finding(number, "画像の代替テキストが空", "画像の代替テキストを入力してください", warning=True)
        elif not destination:
            yield Finding(number, "リンク先が空", f"「{label}」のリンク先を入力してください")
        if destination and (problem := url_problem(destination)):
            yield Finding(number, "URLの体裁", f"「{destination}」: {problem}")
        # リンクのラベルに含まれる画像も検査する。
        if not match["image"] and "![" in label:
            yield from inline_findings(label, number)


def check_pre(source: str) -> list[Finding]:
    findings = []
    previous_level = None
    paragraph_start = None
    for number, line in enumerate(content_lines(source), 1):
        heading_line = number
        level = None
        if atx := ATX_HEADING.match(line):
            level = len(atx[1])
        elif paragraph_start is not None and (underline := SETEXT_UNDERLINE.match(line)):
            level = 1 if underline[1].startswith("=") else 2
            heading_line = paragraph_start

        if level is not None:
            if previous_level is not None and level - previous_level >= 2:
                findings.append(Finding(
                    heading_line, "見出し階層の飛び",
                    f"H{previous_level} から H{level} に進んでいます",
                ))
            previous_level = level
            paragraph_start = None
        elif not line.strip() or PARAGRAPH_INTERRUPT.match(line):
            paragraph_start = None
        elif paragraph_start is None:
            paragraph_start = number

        findings.extend(inline_findings(line, number))

    return sorted(findings, key=lambda finding: finding.line)


def markdown_cell(value: str) -> str:
    return value.replace("\\", "\\\\").replace("|", "\\|").replace("\n", " ")


def markdown_report(findings: list[Finding]) -> str:
    lines = ["| 行 | 指摘 | 詳細 |", "| --- | --- | --- |"]
    for finding in findings:
        check = finding.check + "（警告）" if finding.warning else finding.check
        lines.append(f"| {finding.line} | {check} | {markdown_cell(finding.detail)} |")
    return "\n".join(lines)


POST_COLUMNS = ("参照元", "リンク先", "判定", "詳細")
REQUEST_TIMEOUT = 10
MAX_REDIRECTS = 5
REDIRECT_STATUSES = {301, 302, 303, 307, 308}
BROKEN_STATUSES = {404, 410}
BROKEN = "リンク切れ"
UNKNOWN = "確認不能"
SITEMAP_NAMESPACE = "http://www.sitemaps.org/schemas/sitemap/0.9"
ATOM_NAMESPACE = "http://www.w3.org/2005/Atom"


@dataclass(frozen=True)
class HttpResponse:
    status: int
    body: bytes = b""
    location: str | None = None
    charset: str | None = None


Fetch = Callable[[str, float], HttpResponse]


@dataclass(frozen=True)
class PostFinding:
    source: str
    destination: str
    verdict: str
    detail: str

    def cells(self) -> tuple[str, str, str, str]:
        return self.source, self.destination, self.verdict, self.detail


class PostInputError(ValueError):
    pass


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def request_timed_out(_signum, _frame):
    raise TimeoutError


@contextmanager
def request_deadline(timeout: float) -> Iterator[None]:
    """POSIX の CLI では DNS から本文受信までの経過時間を制限する。"""
    if (
        not hasattr(signal, "setitimer")
        or current_thread() is not main_thread()
        or any(signal.getitimer(signal.ITIMER_REAL))
    ):
        yield
        return

    previous = signal.signal(signal.SIGALRM, request_timed_out)
    try:
        signal.setitimer(signal.ITIMER_REAL, timeout)
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)


def fetch_http(url: str, timeout: float) -> HttpResponse:
    """GET の応答を1回取得する。リダイレクト先は呼び出し側で判断する。"""
    opener = build_opener(NoRedirect())
    with request_deadline(timeout):
        try:
            with opener.open(url, timeout=timeout) as response:
                return HttpResponse(
                    response.status, response.read(),
                    charset=response.headers.get_content_charset(),
                )
        except HTTPError as error:
            with error:
                return HttpResponse(error.code, location=error.headers.get("Location"))


def http_url(value: str, base: str = "") -> tuple[str, str] | None:
    """HTTP(S) URL とホストを返し、比較に不要なフラグメントを除く。"""
    value = value.strip().partition("#")[0]
    if any(character.isspace() or ord(character) < 32 for character in value):
        return None
    try:
        parts = urlsplit(urljoin(base, value))
        parts.port  # 不正なポート表記は対象外。
        host = parts.hostname
    except ValueError:
        return None
    if parts.scheme not in ("http", "https") or not host or parts.username is not None:
        return None
    return parts._replace(netloc=parts.netloc.lower(), fragment="").geturl(), host


def read_url(
    url: str, host: str, fetch: Callable[[str], tuple[HttpResponse | None, str]],
) -> tuple[str, HttpResponse | None, str]:
    """同一ホストの転送を追い、最終 URL と応答または失敗理由を返す。"""
    for redirects in range(MAX_REDIRECTS + 1):
        response, detail = fetch(url)
        if response is None:
            return url, None, detail

        if response.status not in REDIRECT_STATUSES:
            return url, response, f"HTTP {response.status}"
        if not response.location:
            return url, None, "リダイレクト先が指定されていません"
        target = http_url(response.location, url)
        if target is None:
            return url, None, "リダイレクト先の URL が無効です"
        if target[1] != host:
            return url, None, "別ホストへのリダイレクト"
        if redirects == MAX_REDIRECTS:
            return url, None, f"リダイレクトが上限の {MAX_REDIRECTS} 回を超えました"
        url = target[0]
    raise AssertionError("リダイレクトの処理が終了していません")


def article_values(xml: bytes, kind: str) -> Iterator[str]:
    """選択された XML 形式から記事 URL を列挙する。"""
    try:
        root = ElementTree.fromstring(xml)
    except (ElementTree.ParseError, LookupError, ValueError) as error:
        raise PostInputError("入力 XML を解析できません。") from error

    if kind == "sitemap":
        for namespace in (f"{{{SITEMAP_NAMESPACE}}}", ""):
            if root.tag == f"{namespace}urlset":
                for element in root.findall(f"{namespace}url/{namespace}loc"):
                    if element.text:
                        yield element.text
                return
    elif root.tag == "rss" and root.find("channel") is not None:
        for element in root.findall("channel/item/link"):
            if element.text:
                yield element.text
        return
    else:
        for namespace in (f"{{{ATOM_NAMESPACE}}}", ""):
            if root.tag == f"{namespace}feed":
                for entry in root.findall(f"{namespace}entry"):
                    for link in entry.findall(f"{namespace}link"):
                        if link.get("rel", "alternate") == "alternate" and link.get("href"):
                            yield link.attrib["href"]
                            break
                return
    raise PostInputError("指定した入力形式に対応していません。")


class ArticleLinks(HTMLParser):
    def __init__(self):
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in ("a", "area"):
            for name, value in attrs:
                if name == "href" and value is not None:
                    self.hrefs.append(value)
                    break


def internal_urls(values: Iterator[str], base: str, host: str) -> Iterator[str]:
    for value in values:
        if target := http_url(value, base):
            if target[1] == host:
                yield target[0]


def classify_link(response: HttpResponse | None) -> str | None:
    if response is None:
        return UNKNOWN
    if response.status in BROKEN_STATUSES:
        return BROKEN
    return None if 200 <= response.status < 300 else UNKNOWN


def check_post(kind: str, url: str, fetch: Fetch = fetch_http) -> tuple[int, list[PostFinding]]:
    input_target = http_url(url)
    if input_target is None:
        raise PostInputError("入力には有効な HTTP(S) URL を指定してください。")
    input_url, host = input_target

    @cache
    def get(target: str) -> tuple[HttpResponse | None, str]:
        try:
            return fetch(target, REQUEST_TIMEOUT), ""
        except (OSError, HTTPException, ValueError) as error:
            # 通信失敗も保持して、参照元が変わっても同じ URL を再取得しない。
            reason = error.reason if isinstance(error, URLError) else error
            detail = "タイムアウト" if isinstance(reason, TimeoutError) else "通信に失敗しました"
            return None, detail

    xml_url, xml_response, detail = read_url(input_url, host, get)
    if classify_link(xml_response) is not None:
        raise PostInputError(f"入力 XML を取得できません（{detail}）。")
    assert xml_response is not None

    articles = dict.fromkeys(internal_urls(article_values(xml_response.body, kind), xml_url, host))
    inspected = 0
    findings = []
    for article in articles:
        article_url, response, detail = read_url(article, host, get)
        if classify_link(response) is not None:
            findings.append(PostFinding(article, "", UNKNOWN, f"記事取得失敗（{detail}）"))
            continue
        assert response is not None
        try:
            source = response.body.decode(response.charset or "utf-8-sig", errors="replace")
        except (LookupError, UnicodeError):
            findings.append(PostFinding(article, "", UNKNOWN, "記事の文字コードで読み込めません"))
            continue
        links = ArticleLinks()
        try:
            links.feed(source)
            links.close()
        except (AssertionError, ValueError):
            findings.append(PostFinding(article, "", UNKNOWN, "記事の HTML を解析できません"))
            continue
        inspected += 1
        for link in dict.fromkeys(internal_urls(iter(links.hrefs), article_url, host)):
            _, link_response, detail = read_url(link, host, get)
            if verdict := classify_link(link_response):
                findings.append(PostFinding(article, link, verdict, detail))
    return inspected, findings


def post_summary(inspected: int, findings: list[PostFinding]) -> str:
    broken = sum(finding.verdict == BROKEN for finding in findings)
    return (
        f"検査した記事 {inspected}件 ／ リンク切れ {broken}件 ／ "
        f"確認不能 {len(findings) - broken}件"
    )


def write_post_report(output_format: str, inspected: int, findings: list[PostFinding]) -> None:
    summary = post_summary(inspected, findings)
    if output_format == "csv":
        writer = csv.writer(sys.stdout)
        writer.writerow(POST_COLUMNS)
        writer.writerows(finding.cells() for finding in findings)
        sys.stdout.flush()
        print(summary, file=sys.stderr, flush=True)
    else:
        lines = [summary, "", "| " + " | ".join(POST_COLUMNS) + " |", "| --- | --- | --- | --- |"]
        for finding in findings:
            lines.append("| " + " | ".join(map(markdown_cell, finding.cells())) + " |")
        print("\n".join(lines), flush=True)


class PostArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        raise PostInputError("入力を1つ指定し、出力形式には markdown または csv を指定してください。")


def output_error() -> int:
    # 終了時の再書き込みで終了コードが上書きされるのを防ぐ。
    if sys.stdout is sys.__stdout__:
        with open(os.devnull, "wb") as discarded:
            os.dup2(discarded.fileno(), sys.stdout.fileno())
    print("出力エラー: 検査結果を書き込めません。", file=sys.stderr)
    return 2


def main_post(arguments: list[str], fetch: Fetch = fetch_http) -> int:
    if arguments in (["-h"], ["--help"]):
        print(f"{POST_USAGE}\n公開記事の内部リンクを検査します。")
        return 0

    parser = PostArgumentParser(add_help=False, allow_abbrev=False)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--sitemap", action="append")
    inputs.add_argument("--feed", action="append")
    parser.add_argument("--format", choices=("markdown", "csv"), default="markdown")
    try:
        options = parser.parse_args(arguments)
        kind = "sitemap" if options.sitemap else "feed"
        urls = options.sitemap or options.feed
        if len(urls) != 1:
            parser.error("")
    except PostInputError as error:
        print(f"引数エラー: {error}\n{POST_USAGE}", file=sys.stderr)
        return 2

    try:
        inspected, findings = check_post(kind, urls[0], fetch)
    except PostInputError as error:
        print(f"入力エラー: {error}", file=sys.stderr)
        return 2
    try:
        write_post_report(options.format, inspected, findings)
    except (OSError, UnicodeError):
        return output_error()
    return 1 if findings else 0


def main_pre(arguments: list[str]) -> int:
    if arguments in (["-h"], ["--help"]):
        print(f"{PRE_USAGE}\nローカルの UTF-8 Markdown ファイルを1件検査します。")
        return 0
    if len(arguments) == 2 and arguments[0] == "--":
        path = Path(arguments[1])
    elif len(arguments) == 1 and not arguments[0].startswith("-"):
        path = Path(arguments[0])
    else:
        print(f"引数エラー: pre と入力ファイル1件を指定してください。\n{PRE_USAGE}", file=sys.stderr)
        return 2

    try:
        source = path.read_text(encoding="utf-8-sig")
    except UnicodeDecodeError:
        print(f"入力エラー: 「{path}」は UTF-8 で読み込めません。", file=sys.stderr)
        return 2
    except (OSError, ValueError):
        print(f"入力エラー: 「{path}」を読み込めません。", file=sys.stderr)
        return 2

    findings = check_pre(source)
    try:
        print(markdown_report(findings), flush=True)
    except (OSError, UnicodeError):
        return output_error()
    # 警告だけの場合は終了コード 0（2026-11-21 の決定：空 alt は警告扱い）。
    return 1 if any(not finding.warning for finding in findings) else 0


def main(arguments: list[str] | None = None) -> int:
    if arguments is None:
        arguments = sys.argv[1:]
    if arguments[:1] == ["pre"]:
        return main_pre(arguments[1:])
    if arguments[:1] == ["post"]:
        return main_post(arguments[1:])
    if arguments in (["-h"], ["--help"]):
        main_pre(arguments)
        print(POST_USAGE)
        return 0
    print(f"引数エラー: pre または post を指定してください。\n{PRE_USAGE}\n{POST_USAGE}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
