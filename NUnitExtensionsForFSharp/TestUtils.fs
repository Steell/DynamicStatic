module NUnit.FSharp.TestUtils

open NUnit.Framework

let inline (==) (actual:'a) (expected:'a) = Assert.AreEqual(expected, actual)
let inline (!=) (actual:#obj) (expected:#obj) = Assert.AreNotEqual(expected, actual)
let inline (<->) (actual:#obj) expected = Assert.IsInstanceOf(expected, actual)
let inline (<!>) (actual:#obj) expected = Assert.IsNotInstanceOf(expected, actual)

let ``is null`` anObject = Assert.IsNull(anObject)
let ``is not null`` anObject = Assert.NotNull(anObject)

let ``fails with`` (message : string) f = 
    Assert.Throws(
        Is.TypeOf<System.Exception>().And.Message.EqualTo(message), 
        f >> ignore)
    |> ignore

let fails f =
    Assert.Throws(
        Is.TypeOf<System.Exception>(),
        f >> ignore)
    |> ignore